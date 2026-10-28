-- Prove2me | solution 1 for OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:24:09.783997+00:00
-- url     : https://prove2.me/submissions/dad7a542-b96c-4e4f-9bcb-ad331329f16c

import Mathlib
import Definitions.Def_OAIQ18Pg012

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_BoundaryCell
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

theorem Survives.palette_all_colors {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hwn : w≠[]) (hp : ∀ a∈w, a.isPalette) :
    ∀ x, x∈w.map Cell.color := by
  have hr := hw.checker_rollback hc ht hz hp
  have hw' := hw.of_reach hr
  have hn : checkerIdle w≠[] := by simpa [checkerIdle] using hwn
  have hp' : ∀ a∈checkerIdle w, a.isPalette := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hp b hb
  have hi : ∀ a∈checkerIdle w, a.checker=.idle := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    rfl
  have hh := hw'.idle_palette_all_colors hc ht hz hn hp' hi
  simpa [checkerIdle,List.map_map,Function.comp_def] using hh

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ}
lemma split_encoding {α γ : Type*} {f : α→γ} {v : List α} {p a s : List γ}
    (hv : v.map f=p++a++s) : ∃p' a' s', v=p'++a'++s' ∧ p'.map f=p ∧ a'.map f=a ∧ s'.map f=s := by
  obtain ⟨u,s',rfl,hu,hs⟩ := List.map_eq_append_iff.mp hv
  obtain ⟨p',a',rfl,hp,ha⟩ := List.map_eq_append_iff.mp hu
  exact ⟨p',a',s',rfl,hp,ha,hs⟩
lemma step_from_encoding (hh : 4≤h) {S : Schedule (2^h)} {v : List (Cell (2^h))}
    {w : List (Raw h)} (he : Step (by omega) S d (v.map encode) w) :
    ∃ w', w=w'.map encode ∧ FiniteTable.Step S d v w' := by
  obtain ⟨p,s,a,b,hv,rfl,he⟩ := he
  obtain ⟨p',a',s',rfl,hp,ha,hs⟩ := split_encoding hv
  obtain ⟨_,b',_,hb,_⟩ := replacement_has_encodings hh S d a b he
  refine ⟨p'++b'++s',by simp [hp,hb,hs],p',s',a',b',rfl,rfl,?_⟩
  apply (replacement_encode hh S d a' b').mp
  simpa only [ha,←hb] using he
lemma reach_from_encoding (hh : 4≤h) {S : Schedule (2^h)} {v : List (Cell (2^h))}
    {w : List (Raw h)} (he : Reach (by omega) S d (v.map encode) w) :
    ∃ w', w=w'.map encode ∧ FiniteTable.Reach S d v w' := by
  induction he with
  | refl => exact ⟨v,rfl,.refl⟩
  | tail h e ih =>
    obtain ⟨u,rfl,hu⟩ := ih
    obtain ⟨w',rfl,he⟩ := step_from_encoding hh e
    exact ⟨w',rfl,hu.tail he⟩
lemma survives_encode_iff (hh : 4≤h) {S : Schedule (2^h)} (w : List (Cell (2^h))) :
    Survives (by omega) S d (w.map encode) ↔ FiniteTable.Survives S d w := by
  constructor
  · intro hw p z s hr hz
    exact hw (p.map encode) (z.map encode) (s.map encode)
      (by simpa using reach_encode hh hr) ((zero_encode hh S d z).mpr hz)
  · intro hw p z s hr hz
    obtain ⟨v,hv,hr⟩ := reach_from_encoding hh hr
    obtain ⟨p',z',s',rfl,hp,hz',hs⟩ := split_encoding hv.symm
    apply hw p' z' s' hr
    apply (zero_encode hh S d z').mp
    simpa only [hz'] using hz
end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma survives_iff_not_vanishes (w : List (Raw h)) :
    Survives hh S d w ↔ ¬(algebraTable hh S d).Vanishes (FreeMonoid.ofList w) := by
  constructor
  · intro hw ⟨p,z,s,hz,hr⟩
    have he : Reach hh S d w (p.toList++z.toList++s.toList) := reach_iff_table.mpr hr
    exact hw p.toList z.toList s.toList he hz
  · intro hw p z s hr hz
    exact hw ⟨FreeMonoid.ofList p,FreeMonoid.ofList z,FreeMonoid.ofList s,hz,reach_iff_table.mp hr⟩
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.Cancellation

open scoped BigOperators

variable {K : Type u} [CommRing K] [CharP K 2]

theorem alternating_eq_zero_of_card_lt {S : Type u} [CommSemiring S]
    {V : Type v} [AddCommMonoid V] [Module S V]
    {W : Type w} [AddCommMonoid W] [Module S W]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ S V) (f : AlternatingMap S V W ι)
    (h : Fintype.card κ < Fintype.card ι) : f = 0 := by
  apply b.ext_alternating
  intro t ht
  exact ((not_le_of_gt h) (Fintype.card_le_of_injective t ht)).elim

lemma sign_smul_matrix {d : ℕ} (σ : ℤˣ) (X : Matrix (Fin d) (Fin d) K) :
    σ • X = X := by
  rcases Int.units_eq_one_or σ with h | h
  · rw [h, one_smul]
  · rw [h, Units.smul_def]
    change (-1 : ℤ) • X = X
    rw [neg_one_zsmul]
    ext i j
    exact CharTwo.neg_eq (X i j)

theorem alternatingSum_eq_zero {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) K) (h : d ^ 2 < m) :
    alternatingSum X = 0 := by
  let f := MultilinearMap.mkPiAlgebraFin K m (Matrix (Fin d) (Fin d) K)
  have hz : MultilinearMap.alternatization f = 0 :=
    alternating_eq_zero_of_card_lt (Matrix.stdBasis K (Fin d) (Fin d)) _ (by
      simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h)
  have hv := congrArg (fun F : AlternatingMap K
    (Matrix (Fin d) (Fin d) K) (Matrix (Fin d) (Fin d) K) (Fin m) => F X) hz
  simpa only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    sign_smul_matrix, MultilinearMap.mkPiAlgebraFin_apply, AlternatingMap.zero_apply,
    alternatingSum, Function.comp_def, f] using hv

end SourceBurnside.Cancellation

namespace SourceBurnside.Cancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ : Type*} {K : Type*} [CommRing K] [CharP K 2]

omit [CharP K 2] in
lemma chunkWeight_append {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K) (s t : List Γ) :
    chunkWeight W (s ++ t) = chunkWeight W s * chunkWeight W t := by
  simp [chunkWeight]

lemma perm_of_key_eq {p q : Packet Γ} (h : p.key = q.key) :
    p.before = q.before ∧ p.after = q.after ∧ p.inside.Perm q.inside := by
  have hp := congrArg Prod.fst h
  have hq := congrArg (fun x => x.2.1) h
  have hi := congrArg (fun x => x.2.2) h
  exact ⟨hp, hq, Quotient.exact hi⟩

lemma packet_perm_exists (s : List Γ) (hs : s.Nodup) (t : List Γ) (ht : t.Perm s) :
    ∃ σ : Equiv.Perm (Fin s.length), List.ofFn (s.get ∘ σ) = t := by
  let f : Fin t.length → Γ := t.get
  have hlen := ht.length_eq
  let e : Fin t.length ≃ Fin s.length := finCongr hlen
  have hf : Function.Injective f := List.nodup_iff_injective_get.mp (ht.nodup_iff.mpr hs)
  have hg : Function.Injective s.get := List.nodup_iff_injective_get.mp hs
  let τ : Fin t.length ≃ Fin s.length := Equiv.ofBijective
    (fun i => ⟨s.idxOf (t.get i), List.idxOf_lt_length_iff.mpr (ht.mem_iff.mp (List.get_mem t i))⟩)
    (by
      constructor
      · intro i j hij
        apply hf
        have hij' := congrArg (fun x : Fin s.length => s.get x) hij
        simpa [f] using hij'
      · intro j
        have hm : s.get j ∈ t := ht.mem_iff.mpr (List.get_mem s j)
        refine ⟨⟨t.idxOf (s.get j), List.idxOf_lt_length_iff.mpr hm⟩, ?_⟩
        apply hg
        simp)
  refine ⟨e.symm.trans τ, ?_⟩
  apply List.ext_getElem
  · simp
    exact hlen.symm
  · intro i hi hj
    simp only [List.getElem_ofFn, Function.comp_apply, Equiv.trans_apply]
    simp [τ, e]

lemma packet_perm_injective (s : List Γ) (hs : s.Nodup) :
    Function.Injective (fun σ : Equiv.Perm (Fin s.length) => List.ofFn (s.get ∘ σ)) := by
  intro σ τ h
  have he := List.ofFn_injective h
  apply Equiv.ext
  intro i
  exact List.nodup_iff_injective_get.mp hs (congrFun he i)

lemma sum_packet_permutations {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K)
    (s : List Γ) (hm : d^2 < s.length) :
    (∑ σ : Equiv.Perm (Fin s.length), chunkWeight W (List.ofFn (s.get ∘ σ))) = 0 := by
  simpa only [chunkWeight, List.map_ofFn, Function.comp_def, alternatingSum] using
    (alternatingSum_eq_zero (fun i : Fin s.length => W (s.get i)) hm)

lemma Packet.reorder_injective (p : Packet Γ) (hp : p.inside.Nodup) :
    Function.Injective p.reorder := by
  intro σ τ h
  apply packet_perm_injective p.inside hp
  exact List.append_cancel_left (List.append_cancel_right h)

lemma sum_reorder_weight {d : ℕ} (W : Γ → Matrix (Fin d) (Fin d) K)
    (p : Packet Γ) (hm : d^2 < p.inside.length) :
    (∑ σ : Equiv.Perm (Fin p.inside.length), chunkWeight W (p.reorder σ)) = 0 := by
  simp only [Packet.reorder, chunkWeight_append]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_packet_permutations W p.inside hm,
    mul_zero, zero_mul]

theorem packet_cancellation {d : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (S : Finset (List Γ)) (W : Γ → Matrix (Fin d) (Fin d) K)
    (value : List Γ → V) (pick : List Γ → Packet Γ)
    (joins : ∀ s ∈ S, (pick s).join = s)
    (nodup : ∀ s ∈ S, (pick s).inside.Nodup)
    (long : ∀ s ∈ S, d^2 < (pick s).inside.length)
    (closed : ∀ s ∈ S, ∀ σ, (pick s).reorder σ ∈ S)
    (stable : ∀ s ∈ S, ∀ σ, (pick ((pick s).reorder σ)).key = (pick s).key)
    (same_value : ∀ s ∈ S, ∀ σ, value ((pick s).reorder σ) = value s)
    (i j : Fin d) :
    (∑ s ∈ S, chunkWeight W s i j • value s) = 0 := by
  let key := fun s => (pick s).key
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image key)
    (fun s hs => Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    (fun s => chunkWeight W s i j • value s)]
  apply Finset.sum_eq_zero
  intro z hz
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
  have hfiber : S.filter (fun t => key t = key s) =
      Finset.univ.image (pick s).reorder := by
    ext t
    constructor
    · intro ht
      obtain ⟨htS,htkey⟩ := Finset.mem_filter.mp ht
      obtain ⟨hb,ha,hp⟩ := perm_of_key_eq htkey
      obtain ⟨σ,hσ⟩ := packet_perm_exists (pick s).inside (nodup s hs) (pick t).inside hp
      refine Finset.mem_image.mpr ⟨σ,Finset.mem_univ _,?_⟩
      rw [Packet.reorder, hσ, ← hb, ← ha]
      exact joins t htS
    · intro ht
      obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_filter.mpr ⟨closed s hs σ, stable s hs σ⟩
  rw [hfiber, Finset.sum_image]
  · simp_rw [same_value s hs]
    rw [← Finset.sum_smul]
    have hw := congrArg (fun A : Matrix (Fin d) (Fin d) K => A i j)
      (sum_reorder_weight W (pick s) (long s hs))
    simp only [Matrix.sum_apply, Matrix.zero_apply] at hw
    rw [hw, zero_smul]
  · exact (Packet.reorder_injective (pick s) (nodup s hs)).injOn

end
end SourceBurnside.Cancellation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_PacketIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.PacketIntervals
variable {Γ : Type*}

lemma total_perm (len : Γ → ℕ) {s t : List Γ} (h : s.Perm t) :
    total len s = total len t := (h.map len).sum_eq

lemma floorSplit_join (len : Γ → ℕ) (s : List Γ) (N : ℕ) :
    (floorSplit len s N).1 ++ (floorSplit len s N).2 = s := by
  induction s generalizing N with
  | nil => rfl
  | cons c s ih =>
    simp only [floorSplit]
    split
    · simpa using congrArg (List.cons c) (ih (N-len c))
    · rfl

lemma ceilSplit_join (len : Γ → ℕ) (s : List Γ) (N : ℕ) :
    (ceilSplit len s N).1 ++ (ceilSplit len s N).2 = s := by
  induction s generalizing N with
  | nil => rfl
  | cons c s ih =>
    simp only [ceilSplit]
    split
    · rfl
    · split
      · rfl
      · simpa using congrArg (List.cons c) (ih (N-len c))

lemma floorSplit_bound (len : Γ → ℕ) (s : List Γ) (N : ℕ) :
    total len (floorSplit len s N).1 ≤ N := by
  induction s generalizing N with
  | nil => simp [floorSplit]
  | cons c s ih =>
    simp only [floorSplit]
    split
    · simp only [total_cons]
      have := ih (N-len c)
      omega
    · simp

lemma floorSplit_next (len : Γ → ℕ) (s : List Γ) (N : ℕ) (c : Γ) (t : List Γ)
    (h : (floorSplit len s N).2 = c::t) :
    N < total len (floorSplit len s N).1 + len c := by
  induction s generalizing N with
  | nil => simp [floorSplit] at h
  | cons a s ih =>
    simp only [floorSplit] at *
    by_cases ha : len a ≤ N
    · simp only [ite_eq_left ha, total_cons] at h ⊢
      have := ih (N-len a) h
      omega
    · simp only [ite_eq_right ha, total_nil, zero_add] at h ⊢
      cases h
      omega

lemma floorSplit_prefix (len : Γ → ℕ) (p s : List Γ) (N : ℕ)
    (hp : total len p ≤ N)
    (hs : ∀ c t, s = c::t → N < total len p + len c) :
    floorSplit len (p++s) N = (p,s) := by
  induction p generalizing N with
  | nil =>
    cases s with
    | nil => rfl
    | cons c t =>
      have hc := hs c t rfl
      simp [floorSplit, Nat.not_le.mpr (by simpa using hc)]
  | cons c p ih =>
    have hc : len c ≤ N := by simpa using le_trans (Nat.le_add_right (len c) (total len p)) hp
    simp only [List.cons_append, floorSplit, ite_eq_left hc]
    rw [ih (N-len c) (by simp only [total_cons] at hp; omega) (by
      intro a t ht
      have := hs a t ht
      simp only [total_cons] at this
      omega)]

lemma ceilSplit_zero (len : Γ → ℕ) (s : List Γ) : ceilSplit len s 0 = ([],s) := by
  cases s <;> simp [ceilSplit]

lemma ceilSplit_reaches (len : Γ → ℕ) (s : List Γ) (N : ℕ) (hN : N ≤ total len s) :
    N ≤ total len (ceilSplit len s N).1 := by
  induction s generalizing N with
  | nil => simpa [ceilSplit] using hN
  | cons c s ih =>
    simp only [ceilSplit]
    split
    · simp_all
    · split
      · simpa
      · simp only [total_cons]
        have := ih (N-len c) (by simp only [total_cons] at hN; omega)
        omega

lemma ceilSplit_before (len : Γ → ℕ) (s : List Γ) (N : ℕ) (hN : 0 < N)
    (hfit : N ≤ total len s) :
    total len (ceilSplit len s N).1.dropLast < N := by
  induction s generalizing N with
  | nil => simp at hfit; omega
  | cons c s ih =>
    simp only [ceilSplit, ite_eq_right (Nat.ne_of_gt hN)]
    split
    · simpa
    · have hsmall : len c < N := by omega
      have hfit' : N-len c ≤ total len s := by simp only [total_cons] at hfit; omega
      have hr := ceilSplit_reaches len s (N-len c) hfit'
      have he : (ceilSplit len s (N-len c)).1 ≠ [] := by
        intro he
        simp only [he, total_nil] at hr
        omega
      have hb := ih (N-len c) (by omega) hfit'
      rw [List.dropLast_cons_of_ne_nil he, total_cons]
      omega

lemma ceilSplit_prefix (len : Γ → ℕ) (p s : List Γ) (N : ℕ)
    (hp : N ≤ total len p)
    (hprev : (p=[] ∧ N=0) ∨ (p≠[] ∧ total len p.dropLast < N)) :
    ceilSplit len (p++s) N = (p,s) := by
  induction p generalizing N with
  | nil =>
    have : N=0 := by simpa using hp
    subst N
    exact ceilSplit_zero len s
  | cons c p ih =>
    have hN : 0 < N := by
      rcases hprev with h|h
      · simp at h
      · omega
    simp only [List.cons_append, ceilSplit, ite_eq_right (Nat.ne_of_gt hN)]
    cases p with
    | nil =>
      have hc : N ≤ len c := by simpa using hp
      simp [hc]
    | cons a t =>
      have hprev' : total len (a::t).dropLast + len c < N := by
        rcases hprev with h|h
        · simp at h
        · simpa [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), Nat.add_comm] using h.2
      have hc : ¬ N ≤ len c := by omega
      rw [ite_eq_right hc, ih (N-len c) (by change N ≤ len c + total len (a::t) at hp; omega)
        (Or.inr ⟨List.cons_ne_nil _ _, by omega⟩)]

lemma ceilSplit_empty_or_before (len : Γ → ℕ) (s : List Γ) (N : ℕ)
    (hfit : N ≤ total len s) :
    ((ceilSplit len s N).1 = [] ∧ N = 0) ∨
    ((ceilSplit len s N).1 ≠ [] ∧ total len (ceilSplit len s N).1.dropLast < N) := by
  by_cases hN : N=0
  · simp [hN, ceilSplit_zero]
  · right
    have hr := ceilSplit_reaches len s N hfit
    have hb := ceilSplit_before len s N (by omega) hfit
    refine ⟨?_, hb⟩
    intro he
    simp [he] at hr
    omega

lemma ceilSplit_overshoot (len : Γ → ℕ) (s : List Γ) (N b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) :
    total len (ceilSplit len s N).1 ≤ N+b := by
  induction s generalizing N with
  | nil => simp [ceilSplit]
  | cons c s ih =>
    have hc := hb c (by simp)
    have hs : ∀ a ∈ s, len a ≤ b := fun a ha => hb a (by simp [ha])
    simp only [ceilSplit]
    split
    · simp
    · split
      · simpa using le_trans hc (Nat.le_add_left b N)
      · simp only [total_cons]
        have := ih (N-len c) hs
        omega

lemma floorSplit_defect (len : Γ → ℕ) (s : List Γ) (N b : ℕ)
    (hfit : N ≤ total len s) (hb : ∀ c ∈ s, len c ≤ b) :
    N ≤ total len (floorSplit len s N).1 + b := by
  have hj := floorSplit_join len s N
  cases hr : (floorSplit len s N).2 with
  | nil =>
    rw [hr, List.append_nil] at hj
    rw [hj]
    omega
  | cons c t =>
    have hn := floorSplit_next len s N c t hr
    have hc : c ∈ s := by rw [← hj, hr]; simp
    have := hb c hc
    omega

lemma select_join (len : Γ → ℕ) (s : List Γ) (a e : ℕ) :
    (select len s a e).join = s := by
  simp only [select, Selection.join, List.append_assoc, floorSplit_join, ceilSplit_join]

lemma select_before_bound (len : Γ → ℕ) (s : List Γ) (a e b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) :
    total len (select len s a e).before ≤ a+b :=
  ceilSplit_overshoot len s a b hb

lemma select_inside_bound (len : Γ → ℕ) (s : List Γ) (a e b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) (ha : a+b ≤ e) (he : e ≤ total len s) :
    e-a ≤ total len (select len s a e).inside + 2*b := by
  have hc := ceilSplit_overshoot len s a b hb
  have hj := ceilSplit_join len s a
  have ht : total len s = total len (ceilSplit len s a).1 +
      total len (ceilSplit len s a).2 := by
    simpa only [total_append] using congrArg (total len) hj.symm
  have hfit : e-total len (ceilSplit len s a).1 ≤ total len (ceilSplit len s a).2 := by omega
  have hb' : ∀ c ∈ (ceilSplit len s a).2, len c ≤ b := by
    intro c hm
    apply hb
    rw [← hj]
    exact List.mem_append_right _ hm
  have hf := floorSplit_defect len (ceilSplit len s a).2
    (e-total len (ceilSplit len s a).1) b hfit hb'
  change e-a ≤ total len (floorSplit len (ceilSplit len s a).2
    (e-total len (ceilSplit len s a).1)).1 + 2*b
  omega

lemma select_permute (len : Γ → ℕ) (s : List Γ) (a e : ℕ)
    (hfit : a ≤ total len s) (t : List Γ)
    (ht : t.Perm (select len s a e).inside) :
    select len ((select len s a e).before ++ t ++ (select len s a e).after) a e =
      ⟨(select len s a e).before,t,(select len s a e).after⟩ := by
  let p := ceilSplit len s a
  let q := floorSplit len p.2 (e-total len p.1)
  have hp := ceilSplit_prefix len p.1 (t++q.2) a
    (ceilSplit_reaches len s a hfit) (ceilSplit_empty_or_before len s a hfit)
  have hq := floorSplit_prefix len t q.2 (e-total len p.1)
    (by rw [total_perm len ht]; exact floorSplit_bound len p.2 _)
    (by
      intro c r hr
      rw [total_perm len ht]
      exact floorSplit_next len p.2 _ c r hr)
  change select len (p.1 ++ t ++ q.2) a e = ⟨p.1,t,q.2⟩
  simp only [select, List.append_assoc, hp, hq]

lemma total_le_length_mul (len : Γ → ℕ) (s : List Γ) (b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) : total len s ≤ s.length*b := by
  induction s with
  | nil => simp
  | cons c s ih =>
    have hc := hb c (by simp)
    have hs := ih (fun a ha => hb a (by simp [ha]))
    simp only [total_cons, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem select_long (len : Γ → ℕ) (s : List Γ) (a e b d : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) (he : e ≤ total len s)
    (hlong : b*(d^2+3) < e-a) :
    d^2 < (select len s a e).inside.length := by
  have ha : a+b ≤ e := by
    have hmul : b ≤ b*(d^2+3) := by nlinarith
    omega
  have hr := select_inside_bound len s a e b hb ha he
  have hm : ∀ c ∈ (select len s a e).inside, len c ≤ b := by
    intro c hc
    apply hb
    rw [← select_join len s a e, Selection.join]
    simp [hc]
  have ht := total_le_length_mul len (select len s a e).inside b hm
  by_contra hn
  have hle : (select len s a e).inside.length ≤ d^2 := by omega
  have hmul := Nat.mul_le_mul_right b hle
  nlinarith

end SourceBurnside.PacketIntervals

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T A : Type*}

lemma length_spell (label : Γ → List α) (s : List Γ) :
    (spell label s).length = PacketIntervals.total (fun c => (label c).length) s := by
  induction s with
  | nil => rfl
  | cons c s ih => simpa [spell] using congrArg (fun x => (label c).length + x) ih

lemma spell_perm (label : Γ → List α) {s t : List Γ} (h : s.Perm t) :
    (spell label s).Perm (spell label t) := h.flatMap (fun _ _ => List.Perm.refl _)

lemma nodup_of_spell_nodup (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (s : List Γ) (h : (spell label s).Nodup) : s.Nodup := by
  apply (List.nodup_flatMap.mp h).2.imp
  intro a b hab he
  subst b
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (label a) (hne a)
  exact List.disjoint_left.mp hab hx hx

lemma interval_sublist (p s q : List α) (a e : ℕ) (ha : a ≤ p.length)
    (he : p.length+s.length ≤ e) :
    s.Sublist (((p++s++q).drop a).take (e-a)) := by
  have ha' : a ≤ (p++s).length := by simp; omega
  rw [List.drop_append_of_le_length ha', List.drop_append_of_le_length ha]
  rw [List.take_append]
  have hk : ((p.drop a)++s).length ≤ e-a := by
    simp only [List.length_append, List.length_drop]
    omega
  rw [(List.take_eq_self_iff _).mpr hk]
  exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)

lemma select_spelling_sublist (label : Γ → List α) (s : List Γ) (a e : ℕ)
    (ha : a ≤ (spell label s).length)
    (hae : PacketIntervals.total (fun c => (label c).length)
      (PacketIntervals.select (fun c => (label c).length) s a e).before ≤ e) :
    (spell label (PacketIntervals.select (fun c => (label c).length) s a e).inside).Sublist
      (((spell label s).drop a).take (e-a)) := by
  let len := fun c => (label c).length
  let p := PacketIntervals.select len s a e
  have hj : spell label s = spell label p.before ++ spell label p.inside ++ spell label p.after := by
    rw [← PacketIntervals.select_join len s a e]
    simp only [PacketIntervals.Selection.join, spell_append]
    rfl
  rw [hj]
  have hlo : a ≤ (spell label p.before).length := by
    rw [length_spell]
    exact PacketIntervals.ceilSplit_reaches len s a (by simpa [length_spell] using ha)
  have hhi : (spell label p.before).length+(spell label p.inside).length ≤ e := by
    rw [length_spell, length_spell]
    have hf := PacketIntervals.floorSplit_bound len (PacketIntervals.ceilSplit len s a).2
      (e-PacketIntervals.total len (PacketIntervals.ceilSplit len s a).1)
    change PacketIntervals.total len p.inside ≤ e-PacketIntervals.total len p.before at hf
    change PacketIntervals.total len p.before ≤ e at hae
    dsimp [len] at hf hae
    omega
  exact interval_sublist _ _ _ a e hlo hhi

lemma erased_eq_of_perm_uniform (erase : α → T) (t : T) {s r : List α}
    (h : s.Perm r) (hu : ∀ x ∈ s, erase x = t) : s.map erase = r.map erase := by
  have hs : s.map erase = List.replicate s.length t := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, by simpa using hu⟩
  have hr : r.map erase = List.replicate r.length t := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, by simpa using (fun x hx => hu x (h.mem_iff.mpr hx))⟩
  rw [hs,hr,h.length_eq]

variable [Monoid A]

lemma eval_perm_uniform (f : α → A) (erase : α → T) (t : T)
    (hc : ∀ x y, erase x = t → erase y = t → Commute (f x) (f y))
    {s r : List α} (h : s.Perm r) (hu : ∀ x ∈ s, erase x = t) : eval f s = eval f r := by
  apply (h.map f).prod_eq'
  rw [List.pairwise_map]
  exact List.pairwise_of_forall_mem_list (fun x hx y hy => hc x y (hu x hx) (hu y hy))

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T : Type*}

lemma pickPacket_join (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (s : List Γ) : (pickPacket label erase range s).join = s :=
  PacketIntervals.select_join _ _ _ _

lemma reordered_perm (p : Cancellation.Packet Γ) (s : List Γ) (hj : p.join = s)
    (σ : Equiv.Perm (Fin p.inside.length)) : (p.reorder σ).Perm s := by
  rw [← hj]
  have h : (List.ofFn (p.inside.get ∘ σ)).Perm p.inside := by
    simpa using σ.ofFn_comp_perm p.inside.get
  exact (h.append_left p.before).append_right p.after

lemma pickPacket_stable (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (s : List Γ) (ha : (range ((spell label s).map erase)).1 ≤ (spell label s).length)
    (t : T) (hu : ∀ x ∈ spell label (pickPacket label erase range s).inside, erase x = t)
    (σ : Equiv.Perm (Fin (pickPacket label erase range s).inside.length)) :
    (pickPacket label erase range ((pickPacket label erase range s).reorder σ)).key =
      (pickPacket label erase range s).key := by
  let p := pickPacket label erase range s
  let seq := List.ofFn (p.inside.get ∘ σ)
  have hseq : seq.Perm p.inside := by simpa [seq] using σ.ofFn_comp_perm p.inside.get
  have he : (spell label (p.reorder σ)).map erase = (spell label s).map erase := by
    rw [← pickPacket_join label erase range s]
    simp only [Cancellation.Packet.join, Cancellation.Packet.reorder, spell_append, List.map_append]
    rw [erased_eq_of_perm_uniform erase t (spell_perm label hseq).symm hu]
  have hs := PacketIntervals.select_permute (fun c => (label c).length) s
    (range ((spell label s).map erase)).1 (range ((spell label s).map erase)).2
    (by simpa only [length_spell] using ha) seq hseq
  change (pickPacket label erase range (p.reorder σ)).key = p.key
  unfold pickPacket
  rw [he]
  change (let q := PacketIntervals.select (fun c => (label c).length)
              (p.before++seq++p.after) (range ((spell label s).map erase)).1
              (range ((spell label s).map erase)).2;
          Cancellation.Packet.key ⟨q.before,q.inside,q.after⟩) = p.key
  change PacketIntervals.select (fun c => (label c).length) (p.before++seq++p.after)
    (range ((spell label s).map erase)).1 (range ((spell label s).map erase)).2 =
      ⟨p.before,seq,p.after⟩ at hs
  dsimp only
  rw [hs]
  simp only [Cancellation.Packet.key]
  exact congrArg (fun x : Multiset Γ => (p.before,p.after,x)) (Quotient.sound hseq)

variable {A : Type*} [Monoid A]

lemma pickPacket_same_value (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (f : α → A) (s : List Γ) (t : T)
    (hu : ∀ x ∈ spell label (pickPacket label erase range s).inside, erase x = t)
    (hc : ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (σ : Equiv.Perm (Fin (pickPacket label erase range s).inside.length)) :
    eval f (spell label ((pickPacket label erase range s).reorder σ)) = eval f (spell label s) := by
  let p := pickPacket label erase range s
  have hseq : (List.ofFn (p.inside.get ∘ σ)).Perm p.inside := by
    simpa using σ.ofFn_comp_perm p.inside.get
  have hev := eval_perm_uniform f erase t hc (spell_perm label hseq).symm hu
  conv_rhs => rw [← pickPacket_join label erase range s]
  change eval f (spell label (p.reorder σ)) = eval f (spell label p.join)
  simp only [Cancellation.Packet.join, Cancellation.Packet.reorder, spell_append, eval_append]
  rw [hev]

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T K A : Type*} [Fintype Γ] [CommRing K] [CharP K 2]
  [Ring A] [Algebra K A]

lemma mem_candidates (n : ℕ) (s : List Γ) : s ∈ candidates Γ n ↔ s.length ≤ n := by
  simp only [candidates, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨r,f⟩,rfl⟩
    simp only [List.length_ofFn]
    omega
  · intro hs
    exact ⟨⟨⟨s.length,by omega⟩,s.get⟩,List.ofFn_get s⟩

theorem chunkSum_eq_zero_of_ranges {d b n : ℕ}
    (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (hb : ∀ c, (label c).length ≤ b)
    (erase : α → T) (range : List T → ℕ × ℕ)
    (W : Γ → Matrix (Fin d) (Fin d) K) (f : α → A)
    (hrun : ∀ s : List Γ, (spell label s).length = n → eval f (spell label s) ≠ 0 →
      let a := (range ((spell label s).map erase)).1
      let e := (range ((spell label s).map erase)).2
      e ≤ (spell label s).length ∧ b*(d^2+3) < e-a ∧
      (((spell label s).drop a).take (e-a)).Nodup ∧
      ∃ t : T, (∀ x ∈ ((spell label s).drop a).take (e-a), erase x = t) ∧
        ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (i j : Fin d) : chunkSum label W f n i j = 0 := by
  let Q := (candidates Γ n).filter (fun s => (spell label s).length = n)
  let S := Q.filter (fun s => eval f (spell label s) ≠ 0)
  have hS {s : List Γ} (hs : s ∈ S) :
      s.length ≤ n ∧ (spell label s).length = n ∧ eval f (spell label s) ≠ 0 := by
    obtain ⟨hs,hne⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    exact ⟨(mem_candidates n s).mp hs,hl,hne⟩
  let pick := pickPacket label erase range
  have info (s : List Γ) (hs : s ∈ S) :
      (range ((spell label s).map erase)).1 ≤ (spell label s).length ∧
      (spell label (pick s).inside).Nodup ∧ d^2 < (pick s).inside.length ∧
      ∃ t : T, (∀ x ∈ spell label (pick s).inside, erase x=t) ∧
        ∀ x y, erase x=t → erase y=t → Commute (f x) (f y) := by
    obtain ⟨_,hn,hv⟩ := hS hs
    obtain ⟨he,hl,hd,t,hu,hc⟩ := hrun s hn hv
    let a := (range ((spell label s).map erase)).1
    let e := (range ((spell label s).map erase)).2
    have hmul : b ≤ b*(d^2+3) := by nlinarith
    have ha : a ≤ (spell label s).length := by dsimp [a,e] at *; omega
    have hae : PacketIntervals.total (fun c => (label c).length)
        (PacketIntervals.select (fun c => (label c).length) s a e).before ≤ e := by
      have ht := PacketIntervals.select_before_bound (fun c => (label c).length)
        s a e b (fun c _ => hb c)
      dsimp [a,e] at *
      omega
    have sub := select_spelling_sublist label s a e ha hae
    have lng := PacketIntervals.select_long (fun c => (label c).length) s a e b d
      (fun c _ => hb c) (by simpa only [length_spell] using he) hl
    refine ⟨ha,hd.sublist sub,lng,t,?_,hc⟩
    exact fun x hx => hu x (sub.subset hx)
  have same (s : List Γ) (hs : s ∈ S) (σ : Equiv.Perm (Fin (pick s).inside.length)) :
      eval f (spell label ((pick s).reorder σ)) = eval f (spell label s) := by
    obtain ⟨_,_,_,t,hu,hc⟩ := info s hs
    exact pickPacket_same_value label erase range f s t hu hc σ
  have hz := Cancellation.packet_cancellation S W (fun s => eval f (spell label s)) pick
    (fun s _ => pickPacket_join label erase range s)
    (fun s hs => nodup_of_spell_nodup label hne _ (info s hs).2.1)
    (fun s hs => (info s hs).2.2.1)
    (fun s hs σ => by
      obtain ⟨hlen,hn,hv⟩ := hS hs
      have hp := reordered_perm (pick s) s (pickPacket_join label erase range s) σ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
      · exact (mem_candidates n _).mpr (hp.length_eq.trans_le hlen)
      · exact (spell_perm label hp).length_eq.trans hn
      · rw [same s hs σ]
        exact hv)
    (fun s hs σ => by
      obtain ⟨ha,_,_,t,hu,_⟩ := info s hs
      exact pickPacket_stable label erase range s ha t hu σ)
    same i j
  change (∑ s ∈ Q, Cancellation.chunkWeight W s i j • eval f (spell label s)) = 0
  rw [← hz]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have hv : eval f (spell label s) = 0 := by
    by_contra hv
    exact hs (Finset.mem_filter.mpr ⟨‹s ∈ Q›,hv⟩)
  simp [hv]

end
end SourceBurnside.DirectCancellation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_DirectCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {α T A : Type*} [Ring A]

lemma eval_ne_zero_nodup (f : α → A) (w : List α)
    (hc : ∀ x ∈ w, ∀ y ∈ w, Commute (f x) (f y))
    (hsq : ∀ x ∈ w, f x * f x = 0) (hne : eval f w ≠ 0) : w.Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ht : eval f w ≠ 0 := by
      intro hz
      apply hne
      simp [eval, show (w.map f).prod = 0 from hz]
    refine List.nodup_cons.mpr ⟨?_, ih (fun x hx y hy => hc x (by simp [hx]) y (by simp [hy]))
      (fun x hx => hsq x (by simp [hx])) ht⟩
    intro ha
    obtain ⟨p,q,rfl⟩ := List.mem_iff_append.mp ha
    have hcp : Commute (f a) (eval f p) := by
      apply Commute.list_prod_right
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact hc a (by simp) x (by simp [hx])
    apply hne
    have hsq' := hsq a (by simp)
    change f a * eval f (p ++ a :: q) = 0
    rw [eval_append]
    change f a * (eval f p * (f a * eval f q)) = 0
    rw [← mul_assoc, hcp.eq, mul_assoc, ← mul_assoc (f a), hsq', zero_mul, mul_zero]

lemma interval_eval_ne_zero (f : α → A) (w : List α) (a e : ℕ)
    (hn : eval f w ≠ 0) : eval f ((w.drop a).take (e-a)) ≠ 0 := by
  intro hz
  apply hn
  have he : w = w.take a ++ (w.drop a).take (e-a) ++ (w.drop a).drop (e-a) := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  rw [he, eval_append, eval_append, hz, mul_zero, zero_mul]

lemma firstLongRun_spec (eligible : T → Prop) (q : ℕ) (v : List T)
    (h : ∃ a e, EligibleInterval eligible q v a e) :
    EligibleInterval eligible q v (firstLongRun eligible q v).1
      (firstLongRun eligible q v).2 := by
  simp only [firstLongRun, dite_eq_left h]
  exact Nat.find_spec (Nat.find_spec h)

lemma eligibleInterval_uniform (erase : α → T) (eligible : T → Prop) (q : ℕ)
    (w : List α) (a e : ℕ) (h : EligibleInterval eligible q (w.map erase) a e) :
    ∃ t, eligible t ∧ ∀ x ∈ (w.drop a).take (e-a), erase x=t := by
  obtain ⟨_,_,_,t,ht,he,_,_⟩ := h
  refine ⟨t,ht,?_⟩
  intro x hx
  have hm : erase x ∈ ((w.drop a).take (e-a)).map erase := List.mem_map_of_mem hx
  have hmap : ((w.drop a).take (e-a)).map erase = List.replicate (e-a) t := by
    simpa only [List.map_take, List.map_drop] using he
  rw [hmap] at hm
  exact (List.mem_replicate.mp hm).2

variable {Γ K : Type*} [Fintype Γ] [CommRing K] [CharP K 2] [Algebra K A]

theorem direct_cancellation {d b q N : ℕ}
    (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (hb : ∀ c, (label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀ t, eligible t → ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀ x, eligible (erase x) → f x*f x=0)
    (hlong : ∀ w : List α, N ≤ w.length → eval f w ≠ 0 →
      ∃ a e, EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*(d^2+3) < q)
    (W : Γ → Matrix (Fin d) (Fin d) K) (n : ℕ) (hn : N ≤ n) (i j : Fin d) :
    chunkSum label W f n i j = 0 := by
  apply chunkSum_eq_zero_of_ranges label hne hb erase (firstLongRun eligible q) W f
  intro s hlen hval
  have hs := firstLongRun_spec eligible q ((spell label s).map erase)
    (hlong _ (hlen ▸ hn) hval)
  obtain ⟨t,ht,hu⟩ := eligibleInterval_uniform erase eligible q (spell label s) _ _ hs
  obtain ⟨ha,he,hq,_⟩ := hs
  refine ⟨?_,?_,?_,t,hu,hcomm t ht⟩
  · simpa only [List.length_map] using he
  · nlinarith
  · apply eval_ne_zero_nodup f _
    · intro x hx y hy
      exact hcomm t ht x y (hu x hx) (hu y hy)
    · intro x hx
      exact hsquare x ((hu x hx).symm ▸ ht)
    · exact interval_eval_ne_zero f _ _ _ hval

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.Automaton
open scoped BigOperators
noncomputable section
open Classical

variable {Γ : Type u} {S : Type v} [Semiring S]

lemma card_state [Fintype Γ] [Nonempty Γ] (b : ℕ) :
    Fintype.card (State Γ b) ≤ b * Fintype.card Γ ^ b := by
  calc
    _ ≤ Fintype.card (Σ i : Fin b, Fin i.val → Γ) := Fintype.card_le_of_injective _ stateCode_injective
    _ = ∑ i : Fin b, Fintype.card Γ ^ i.val := by simp
    _ ≤ ∑ _i : Fin b, Fintype.card Γ ^ b := Finset.sum_le_sum (fun i _ => by
      exact Nat.pow_le_pow_right Fintype.card_pos i.isLt.le)
    _ = b * Fintype.card Γ ^ b := by simp

lemma transition_mul [Fintype Γ] {b : ℕ} (hb : 0 < b)
    (W : List Γ → S) (a : Γ) (p : State Γ b) (f : State Γ b → S) :
    (∑ q, transition W a p q * f q) =
      (if h : (p.val ++ [a]).length < b then f ⟨p.val ++ [a], h⟩ else 0) +
        W (p.val ++ [a]) * f (root hb) := by
  simp only [transition, add_mul, Finset.sum_add_distrib]
  congr 1
  · by_cases h : (p.val ++ [a]).length < b
    · rw [dite_eq_left h]
      have he : ∀ q : State Γ b, q.val = p.val ++ [a] ↔ q = ⟨p.val ++ [a], h⟩ :=
        fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      simp only [he, ite_mul, zero_mul, one_mul]
      simp
    · rw [dite_eq_right h]
      apply Finset.sum_eq_zero
      intro q _
      have hq : q.val ≠ p.val ++ [a] := by
        intro heq
        exact h (heq ▸ q.property)
      simp [hq]
  · have he : ∀ q : State Γ b, q.val = [] ↔ q = root hb :=
      fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [he, ite_mul, zero_mul]
    simp

theorem product_transition [Fintype Γ] {b : ℕ} (hb : 0 < b)
    (W : List Γ → S) (w : List Γ) (p : State Γ b) :
    (w.map (transition (b := b) W)).prod p (root hb) = scan b W p.val w := by
  induction w generalizing p with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply, scan]
    congr 1
    exact propext Subtype.ext_iff
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    rw [transition_mul hb W a p]
    simp only [scan]
    split_ifs with h
    · rw [ih ⟨p.val ++ [a], h⟩, ih (root hb)]
      rfl
    · rw [ih (root hb)]
      rfl

lemma freeScan_long {b : ℕ} (hb : 0 < b) (W : List Γ → S)
    (hW : ∀ v, b < v.length → W v = 0) (p w : List Γ) (hp : b ≤ p.length) :
    freeScan W p w = 0 := by
  induction w generalizing p with
  | nil =>
    have hn : p ≠ [] := by intro h; simp [h] at hp; omega
    simp [freeScan, hn]
  | cons a w ih =>
    have hlen : b < (p ++ [a]).length := by simp; omega
    rw [freeScan, ih _ hlen.le, hW _ hlen, zero_mul, add_zero]

lemma scan_eq_freeScan {b : ℕ} (hb : 0 < b) (W : List Γ → S)
    (hW : ∀ v, b < v.length → W v = 0) (p w : List Γ) :
    scan b W p w = freeScan W p w := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
    simp only [scan, freeScan, ih]
    split_ifs with h
    · rfl
    · rw [freeScan_long hb W hW (p ++ [a]) w (by omega)]

lemma partitionWeight_empty (W : List Γ → S) (vs : List (List Γ)) :
    partitionWeight W [] vs = (vs.map W).prod := by cases vs <;> simp [partitionWeight]

lemma sum_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → S) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma freeScan_eq_partitions (W : List Γ → S) (p w : List Γ) :
    freeScan W p w = ((partitions w).map (partitionWeight W p)).sum := by
  induction w generalizing p with
  | nil => simp [freeScan, partitions, partitionWeight]
  | cons a w ih =>
    rw [freeScan, partitions, sum_flatMap]
    simp_rw [ih]
    have hterm : ∀ vs : List (List Γ),
        ((([a] :: vs) :: (match vs with | [] => [] | v :: rest => [(a :: v) :: rest])).map
          (partitionWeight W p)).sum =
          partitionWeight W (p ++ [a]) vs + W (p ++ [a]) * partitionWeight W [] vs := by
      intro vs
      cases vs with
      | nil => simp [partitionWeight]
      | cons v vs => simp [partitionWeight, List.append_assoc, add_comm]
    refine Eq.trans ?_ (congrArg List.sum (List.map_congr_left (fun vs _ => hterm vs)).symm)
    rw [List.sum_map_add]
    congr 1
    induction partitions w with
    | nil => simp
    | cons vs l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem root_product_eq_partitions [Fintype Γ] {b : ℕ} (hb : 0 < b)
    (W : List Γ → S) (hW : ∀ v, b < v.length → W v = 0) (w : List Γ) :
    (w.map (transition (b := b) W)).prod (root hb) (root hb) =
      ((partitions w).map (fun vs => (vs.map W).prod)).sum := by
  rw [product_transition hb, scan_eq_freeScan hb W hW, freeScan_eq_partitions]
  change ((partitions w).map (partitionWeight W [])).sum = _
  congr 2
  funext vs
  exact partitionWeight_empty W vs

lemma partitions_sound {w : List Γ} {vs : List (List Γ)}
    (h : vs ∈ partitions w) : Segments vs w := by
  induction w generalizing vs with
  | nil =>
    simp only [partitions, List.mem_singleton] at h
    subst vs
    simp [Segments]
  | cons a w ih =>
    obtain ⟨ps, hp, hm⟩ := List.mem_flatMap.mp h
    have hs := ih hp
    cases ps with
    | nil =>
      simp only [List.mem_singleton] at hm
      subst vs
      obtain ⟨rfl, _⟩ := hs
      simp [Segments]
    | cons v ps =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · constructor
        · simpa using congrArg (List.cons a) hs.1
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · simp
          · exact hs.2 z hz
      · constructor
        · simpa using congrArg (List.cons a) hs.1
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · simp
          · exact hs.2 z (List.mem_cons_of_mem _ hz)

lemma partitions_complete {w : List Γ} {vs : List (List Γ)}
    (hs : Segments vs w) : vs ∈ partitions w := by
  induction w generalizing vs with
  | nil =>
    cases vs with
    | nil => exact List.mem_singleton_self _
    | cons v vs =>
      have hv := hs.2 v (by simp)
      have ht : v = [] ∧ vs.flatten = [] := by simpa only [List.flatten_cons, List.append_eq_nil_iff] using hs.1
      have : v = [] := ht.1
      contradiction
  | cons a w ih =>
    cases vs with
    | nil => simp [Segments] at hs
    | cons v vs =>
      cases v with
      | nil => exact (hs.2 [] (by simp) rfl).elim
      | cons z zs =>
        have heq : z = a ∧ zs ++ vs.flatten = w := by simpa using hs.1
        obtain ⟨rfl, heq⟩ := heq
        cases zs with
        | nil =>
          have ht : Segments vs w := ⟨by simpa using heq,
            fun t ht => hs.2 t (List.mem_cons_of_mem _ ht)⟩
          apply List.mem_flatMap.mpr
          exact ⟨vs, ih ht, List.mem_cons_self⟩
        | cons z zs =>
          have ht : Segments ((z :: zs) :: vs) w := by
            constructor
            · exact heq
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · simp
              · exact hs.2 t (List.mem_cons_of_mem _ ht)
          apply List.mem_flatMap.mpr
          refine ⟨(z :: zs) :: vs, ih ht, ?_⟩
          simp

theorem mem_partitions_iff {w : List Γ} {vs : List (List Γ)} :
    vs ∈ partitions w ↔ Segments vs w := ⟨partitions_sound, partitions_complete⟩

lemma parent_children (a : Γ) (vs : List (List Γ))
    (hs : ∀ v ∈ vs, v ≠ []) {cs : List (List Γ)} (hc : cs ∈ children a vs) :
    parent cs = vs := by
  cases vs with
  | nil => simp only [children, List.mem_singleton] at hc; subst cs; rfl
  | cons v vs =>
    cases v with
    | nil => exact (hs [] (by simp) rfl).elim
    | cons z zs =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

lemma children_nodup (a : Γ) (vs : List (List Γ))
    (hs : ∀ v ∈ vs, v ≠ []) : (children a vs).Nodup := by
  cases vs with
  | nil => simp [children]
  | cons v vs =>
    have hn := hs v (by simp)
    simp [children, hn]

theorem partitions_nodup (w : List Γ) : (partitions w).Nodup := by
  induction w with
  | nil => simp [partitions]
  | cons a w ih =>
    change ((partitions w).flatMap (children a)).Nodup
    apply List.nodup_flatMap.mpr
    constructor
    · intro vs hv
      exact children_nodup a vs (partitions_sound hv).2
    · apply List.pairwise_iff_get.mpr
      intro i j hij
      apply List.disjoint_left.mpr
      intro cs hci hcj
      have hi := parent_children a ((partitions w).get i)
        (partitions_sound (List.get_mem _ _)).2 hci
      have hj := parent_children a ((partitions w).get j)
        (partitions_sound (List.get_mem _ _)).2 hcj
      have he := (List.nodup_iff_injective_get.mp ih) (hi.symm.trans hj)
      exact (ne_of_lt hij) he

lemma blockTransition_product {b : ℕ} [Fintype Γ] {ι : Type*} [Fintype ι]
    (W : List Γ → Matrix ι ι S) (w : List Γ) :
    (w.map (blockTransition (b := b) W)).prod =
      Matrix.compRingEquiv _ _ _ ((w.map (transition (b := b) W)).prod) := by
  symm
  rw [map_list_prod]
  rw [List.map_map]
  rfl

theorem root_block_eq_partitions {b : ℕ} [Fintype Γ] {ι : Type*} [Fintype ι]
    (hb : 0 < b) (W : List Γ → Matrix ι ι S)
    (hW : ∀ v, b < v.length → W v = 0) (w : List Γ) (i j : ι) :
    (w.map (blockTransition (b := b) W)).prod (root hb, i) (root hb, j) =
      ((partitions w).map (fun vs => (vs.map W).prod)).sum i j := by
  rw [blockTransition_product]
  change ((w.map (transition (b := b) W)).prod (root hb) (root hb)) i j = _
  rw [root_product_eq_partitions hb W hW]

end
end SourceBurnside.Automaton

namespace SourceBurnside.Automaton
open scoped BigOperators
noncomputable section
open Classical
variable {α Γ S : Type*} [Fintype Γ] [Semiring S]

lemma combinedWeight_long (label : Γ → List α) (weight : Γ → S) {b : ℕ}
    (hb : ∀ c, (label c).length ≤ b) (w : List α) (hw : b < w.length) :
    combinedWeight label weight w = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  rw [ite_eq_right]
  intro he
  have := hb c
  rw [he] at this
  omega

lemma product_combinedWeight (label : Γ → List α) (weight : Γ → S)
    (vs : List (List α)) :
    (vs.map (combinedWeight label weight)).prod =
      ∑ cs : Fin vs.length → Γ,
        if List.ofFn (label ∘ cs) = vs then (List.ofFn (weight ∘ cs)).prod else 0 := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.length_cons]
    rw [← (Fin.consEquiv (fun _ : Fin (vs.length+1) => Γ)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, List.map_cons, List.prod_cons,
      List.ofFn_succ, Function.comp_def, Fin.cons_zero, Fin.cons_succ, List.cons.injEq]
    rw [ih]
    change (∑ c, if label c = v then weight c else 0) *
      (∑ cs : Fin vs.length → Γ,
        if List.ofFn (label ∘ cs) = vs then (List.ofFn (weight ∘ cs)).prod else 0) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cs _
    split_ifs <;> simp_all [Function.comp_def]

lemma length_le_flatten_of_nonempty (vs : List (List α))
    (hv : ∀ v ∈ vs, v ≠ []) : vs.length ≤ vs.flatten.length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have hne := hv v (by simp)
    have hp : 0 < v.length := List.length_pos_iff.mpr hne
    have hi := ih (fun t ht => hv t (by simp [ht]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

omit [Fintype Γ] in
lemma identifiers_segments (label : Γ → List α) (hn : ∀ c, label c ≠ [])
    {r : ℕ} (cs : Fin r → Γ) :
    Segments (List.ofFn (label ∘ cs)) ((List.ofFn (label ∘ cs)).flatten) := by
  refine ⟨rfl, ?_⟩
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact hn (cs i)

lemma bounded_product_combinedWeight (label : Γ → List α) (weight : Γ → S)
    (vs : List (List α)) {n : ℕ} (hv : vs.length ≤ n) :
    (∑ s : BoundedSequences Γ n,
      if List.ofFn (label ∘ s.2) = vs then seqWeight weight s else 0) =
      (vs.map (combinedWeight label weight)).prod := by
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (⟨vs.length, Nat.lt_succ_of_le hv⟩ : Fin (n+1))]
  · exact (product_combinedWeight label weight vs).symm
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro cs _
    rw [ite_eq_right]
    intro he
    have he' := congrArg List.length he
    simp only [List.length_ofFn] at he'
    exact hr (Fin.ext he')
  · simp

omit [Fintype Γ] in
lemma spelled_eq_iff_partition (label : Γ → List α) (hn : ∀ c, label c ≠ [])
    {n : ℕ} (s : BoundedSequences Γ n) (w : List α) :
    spelled label s = w ↔ List.ofFn (label ∘ s.2) ∈ partitions w := by
  rw [mem_partitions_iff]
  constructor
  · intro he
    exact ⟨he, (identifiers_segments label hn s.2).2⟩
  · exact fun he => he.1

theorem wordCoefficient_eq_partitions (label : Γ → List α) (hn : ∀ c, label c ≠ [])
    (weight : Γ → S) (w : List α) :
    wordCoefficient label weight w =
      ((partitions w).map (fun vs => (vs.map (combinedWeight label weight)).prod)).sum := by
  have hnod := partitions_nodup w
  rw [← List.sum_toFinset _ hnod]
  simp only [wordCoefficient]
  have expand (vs : List (List α)) (hvs : vs ∈ (partitions w).toFinset) :
      (vs.map (combinedWeight label weight)).prod =
        ∑ s : BoundedSequences Γ w.length,
          if List.ofFn (label ∘ s.2) = vs then seqWeight weight s else 0 := by
    have hs := partitions_sound (List.mem_toFinset.mp hvs)
    apply (bounded_product_combinedWeight label weight vs ?_).symm
    simpa [hs.1] using length_le_flatten_of_nonempty vs hs.2
  rw [Finset.sum_congr rfl expand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have he := spelled_eq_iff_partition label hn s w
  simp only [← List.mem_toFinset] at he
  by_cases h : spelled label s = w
  · rw [ite_eq_left h]
    rw [Finset.sum_eq_single (List.ofFn (label ∘ s.2))]
    · simp
    · intro vs _ hvs
      rw [ite_eq_right (Ne.symm hvs)]
    · exact fun hm => (hm (he.mp h)).elim
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro vs hvs
    rw [ite_eq_right]
    intro heq
    exact h (he.mpr (heq ▸ hvs))

theorem root_block_eq_wordCoefficient [Fintype α] {ι : Type*} [Fintype ι]
    {b : ℕ} (hb : 0 < b) (label : Γ → List α)
    (hn : ∀ c, label c ≠ []) (hl : ∀ c, (label c).length ≤ b)
    (weight : Γ → Matrix ι ι S) (w : List α) (i j : ι) :
    (w.map (blockTransition (b := b) (combinedWeight label weight))).prod
      (root hb, i) (root hb, j) = wordCoefficient label weight w i j := by
  rw [root_block_eq_partitions hb _ (combinedWeight_long label weight hl),
    wordCoefficient_eq_partitions label hn]

omit [Fintype Γ] in
lemma sum_words_eq [Fintype α] (v : List α) (n : ℕ) (c : S) :
    (∑ w : Fin n → α, if List.ofFn w = v then c else 0) =
      if v.length = n then c else 0 := by
  by_cases hv : v.length = n
  · subst n
    rw [ite_eq_left rfl, Finset.sum_eq_single v.get]
    · simp
    · intro w _ hw
      rw [ite_eq_right]
      intro he
      have ht : List.ofFn w = List.ofFn v.get := he.trans (List.ofFn_get v).symm
      exact hw (List.ofFn_injective ht)
    · simp
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro w _
    rw [ite_eq_right]
    intro he
    exact hv ((congrArg List.length he).symm.trans (List.length_ofFn (f := w)))

end
end SourceBurnside.Automaton

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_HierarchyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.HierarchyGrowth
open scoped BigOperators

lemma height_succ (H D n : ℕ) : height H D (n+1) = D * height H D n := by
  simp [height, pow_succ]; ring

lemma exponent_succ (H D d k c n : ℕ) :
    exponent H D d k c (n+1) = k + c * height H D n * k + exponent H D d k c n := by
  simp [exponent, Finset.sum_range_succ]; ring

lemma dimension_bound (H D d k c : ℕ) (s : ℕ → ℕ)
    (hs : ∀ n, s n ≤ 2 ^ (c * height H D n)) (n : ℕ) :
    dimension d k s n ≤ 2 ^ exponent H D d k c n := by
  induction n with
  | zero => simpa [dimension, exponent] using (Nat.lt_two_pow_self (n := d)).le
  | succ n ih =>
    have hk : k ≤ 2^k := (Nat.lt_two_pow_self (n := k)).le
    calc
      dimension d k s (n+1) = k * s n ^ k * dimension d k s n := rfl
      _ ≤ 2^k * (2 ^ (c * height H D n)) ^ k * 2 ^ exponent H D d k c n :=
        Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.pow_le_pow_left (hs n) k)) ih
      _ = 2 ^ exponent H D d k c (n+1) := by
        simp only [← pow_mul, ← pow_add, exponent_succ]

lemma geometric_identity (H D n : ℕ) (hD : 1 ≤ D) :
    H + (D-1) * (∑ i ∈ Finset.range n, height H D i) = height H D n := by
  induction n with
  | zero => simp [height]
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ← Nat.add_assoc, ih, height_succ]
    have hD' : D-1+1 = D := Nat.sub_add_cancel hD
    nlinarith

lemma source_choice (c k D : ℕ) (hD : 10*(c+1)*(k+1) < D) :
    4 ≤ D ∧ 4*k*c ≤ D-1 := by
  constructor
  · nlinarith
  · have hx : 4*k*c < D := by nlinarith
    omega

theorem stopping_index (H D d k c : ℕ) (s : ℕ → ℕ)
    (hH : 1 ≤ H) (hD : 10*(c+1)*(k+1) < D)
    (hs : ∀ n, s n ≤ 2 ^ (c * height H D n)) :
    ∃ n, 400*k*(dimension d k s n)^2 < 2 ^ height H D n := by
  obtain ⟨hD4, hDcharge⟩ := source_choice c k D hD
  let L := 400*k
  let n := 2*L + 4*d + 4*k + 2
  have hn : n < 2^n := Nat.lt_two_pow_self
  have hnheight : n^2 < height H D n := by
    calc
      n^2 < (2^n)^2 := Nat.pow_lt_pow_left hn (by decide)
      _ = 4^n := by rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
      _ ≤ D^n := Nat.pow_le_pow_left hD4 n
      _ ≤ H*D^n := Nat.le_mul_of_pos_left _ hH
  have hfree : 2*L + 4*d + 4*k*n < height H D n := by
    have hnlarge : 2*L + 4*d + 4*k + 2 = n := rfl
    nlinarith
  have hcharge : 4*k*c*(∑ i ∈ Finset.range n, height H D i) ≤ height H D n := by
    have hi := geometric_identity H D n (by omega)
    have hm := Nat.mul_le_mul_right (∑ i ∈ Finset.range n, height H D i) hDcharge
    omega
  have hexp : L + 2 * exponent H D d k c n < height H D n := by
    unfold exponent
    nlinarith
  refine ⟨n, ?_⟩
  calc
    400*k*(dimension d k s n)^2 ≤ 2^L * (2 ^ exponent H D d k c n)^2 :=
      Nat.mul_le_mul (Nat.lt_two_pow_self (n := L)).le
        (Nat.pow_le_pow_left (dimension_bound H D d k c s hs n) 2)
    _ = 2 ^ (L + 2 * exponent H D d k c n) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    _ < 2 ^ height H D n := Nat.pow_lt_pow_right (by decide) hexp

end SourceBurnside.HierarchyGrowth

namespace SourceBurnside.WeightedTests

open scoped BigOperators
noncomputable section
open Classical

variable {Γ : Type u} [Fintype Γ] {R : Type v} [Semiring R]

omit [Fintype Γ] in
lemma length_ge (l : Γ → ℕ) (hl : ∀ c, 1 ≤ l c) {r : ℕ} (v : Fin r → Γ) :
    r ≤ length l v := by
  calc
    r = ∑ _i : Fin r, (1 : ℕ) := by simp
    _ ≤ ∑ i : Fin r, l (v i) := Finset.sum_le_sum (fun i _ => hl (v i))

lemma sum_product_eq_pow (f : Γ → R) (r : ℕ) :
    (∑ v : Fin r → Γ, product f v) = (∑ c, f c) ^ r := by
  induction r with
  | zero => simp [product]
  | succ r ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (r+1) => Γ)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, product, Function.comp_def,
      List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    simp only [product, Function.comp_def] at ih
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ih, pow_succ']

lemma coefficient_lengthPolynomial (l : Γ → ℕ) (f : Γ → R) {n r : ℕ}
    (hr : r ≤ n) :
    (lengthPolynomial l f n).coeff r =
      ∑ v : Fin r → Γ, if length l v = n then product f v else 0 := by
  unfold lengthPolynomial
  simp only [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single r]
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  · intro b _ hbr
    apply Finset.sum_eq_zero
    intro v _
    split_ifs <;> simp [Polynomial.coeff_monomial, hbr]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))).elim

theorem nilpotent_of_eventually_zero_lengthPolynomial
    (l : Γ → ℕ) (hl : ∀ c, 1 ≤ l c) (f : Γ → R)
    (h : ∃ N, ∀ n, N ≤ n → lengthPolynomial l f n = 0) :
    IsNilpotent (∑ c, f c) := by
  obtain ⟨N, hN⟩ := h
  let r := N + 1
  let lens : Finset ℕ := Finset.univ.image (length (r := r) l)
  have hfiber : ∀ n ∈ lens,
      (∑ v : Fin r → Γ, if length l v = n then product f v else 0) = 0 := by
    intro n hn
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hn
    have hrn : r ≤ n := hv ▸ length_ge l hl v
    rw [← coefficient_lengthPolynomial l f hrn, hN n (by omega)]
    exact Polynomial.coeff_zero r
  refine ⟨r, ?_⟩
  rw [← sum_product_eq_pow f r]
  have hp := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := lens)
    (g := length (r := r) l) (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    (product f)
  rw [← hp]
  apply Finset.sum_eq_zero
  intro n hn
  simpa only [Finset.sum_filter] using hfiber n hn

end
end SourceBurnside.WeightedTests

namespace SourceBurnside.Cuts
open Classical
noncomputable section
variable {α : Type*}

lemma parse_join (cut : α → Prop) (w : List α) :
    (parse cut w).1 ++ (parse cut w).2.flatten = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [parse]
    split <;> simpa only [List.nil_append, List.flatten_cons, List.cons_append] using
      congrArg (List.cons a) ih

lemma parse_prefix (cut : α → Prop) (w : List α) : NoCut cut (parse cut w).1 := by
  induction w with
  | nil => simp [parse,NoCut]
  | cons a w ih =>
    by_cases ha : cut a
    · simp [parse,ha,NoCut]
    · simp only [parse,ite_eq_right ha]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih x hx

lemma parse_intervals (cut : α → Prop) (w : List α) :
    ∀ t ∈ (parse cut w).2, Interval cut t := by
  induction w with
  | nil => simp [parse]
  | cons a w ih =>
    by_cases ha : cut a
    · simp only [parse,ite_eq_left ha]
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨a,(parse cut w).1,rfl,ha,parse_prefix cut w⟩
      · exact ih t ht
    · simpa only [parse,ite_eq_right ha] using ih

lemma parse_noCut_append (cut : α → Prop) (p w : List α) (hp : NoCut cut p) :
    parse cut (p++w) = (p++(parse cut w).1,(parse cut w).2) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht : NoCut cut p := fun x hx => hp x (by simp [hx])
    simp only [List.cons_append,parse,ih ht,ite_eq_right ha]

lemma parse_interval_append (cut : α → Prop) (t w : List α) (ht : Interval cut t) :
    parse cut (t++w) = ([],(t++(parse cut w).1)::(parse cut w).2) := by
  obtain ⟨a,p,rfl,ha,hp⟩ := ht
  simp only [List.cons_append,parse,parse_noCut_append cut p w hp,ite_eq_left ha]

lemma parse_intervals_flatten (cut : α → Prop) (ts : List (List α))
    (ht : ∀ t ∈ ts, Interval cut t) : parse cut ts.flatten = ([],ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have h0 := ht t (by simp)
    have h1 := ih (fun u hu => ht u (by simp [hu]))
    simp only [List.flatten_cons,parse_interval_append cut t _ h0,h1,List.append_nil]

theorem parse_language (cut : α → Prop) (p s : List α) (ts : List (List α))
    (hp : NoCut cut p) (hs : Interval cut s) (ht : ∀ t ∈ ts, Interval cut t) :
    parse cut (p++ts.flatten++s) = (p,ts++[s]) := by
  rw [List.append_assoc]
  have h := parse_intervals_flatten cut (ts++[s]) (by
    intro t hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ht t hm
    · simpa using (List.mem_singleton.mp hm) ▸ hs)
  simp only [List.flatten_append,List.flatten_singleton] at h
  rw [parse_noCut_append cut p (ts.flatten++s) hp,h]
  simp

theorem language_injective (cut : α → Prop)
    {p s p' s' : List α} {ts ts' : List (List α)}
    (hp : NoCut cut p) (hs : Interval cut s) (ht : ∀ t ∈ ts, Interval cut t)
    (hp' : NoCut cut p') (hs' : Interval cut s') (ht' : ∀ t ∈ ts', Interval cut t)
    (he : p++ts.flatten++s = p'++ts'.flatten++s') :
    p=p' ∧ ts=ts' ∧ s=s' := by
  have h := congrArg (parse cut) he
  rw [parse_language cut p s ts hp hs ht,parse_language cut p' s' ts' hp' hs' ht'] at h
  have hp0 := congrArg Prod.fst h
  have ht0 := congrArg Prod.snd h
  exact ⟨hp0,List.append_singleton_inj.mp ht0⟩

end
end SourceBurnside.Cuts
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax Cuts
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma token_of_adjacent {t s : List (Cell q)} (ht : Cuts.Interval Cell.Cut t)
    (hs : Cuts.Interval Cell.Cut s) (hw : Survives S d (t++s)) : Token S d t := by
  obtain ⟨b,w,rfl,hb,_⟩ := hs
  exact ⟨ht,b,hb,hw.infix ⟨[],w,by simp⟩⟩
lemma tokens_of_flatten {ts : List (List (Cell q))} {s : List (Cell q)}
    (hs : Cuts.Interval Cell.Cut s) (ht : ∀t∈ts,Cuts.Interval Cell.Cut t)
    (hw : Survives S d (ts.flatten++s)) : ∀t∈ts,Token S d t := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have htt := ht t (by simp)
    have hts := fun u hu => ht u (List.mem_cons_of_mem _ hu)
    have hwts : Survives S d (ts.flatten++s) := hw.infix ⟨t,[],by simp⟩
    have htok : Token S d t := by
      cases ts with
      | nil => exact token_of_adjacent htt hs (by simpa using hw)
      | cons u us =>
        apply token_of_adjacent htt (hts u (by simp))
        exact hw.infix ⟨[],us.flatten++s,by simp [List.append_assoc]⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact htok
    · exact ih hts hwts u hu

theorem Survives.token_decomposition {w : List (Cell q)} (hw : Survives S d w)
    (hlong : 2*fragmentBound q<w.length) :
    ∃p ts s, w=p++ts.flatten++s ∧ Cuts.NoCut Cell.Cut p ∧
      Cuts.Interval Cell.Cut s ∧ p.length≤fragmentBound q ∧ s.length≤fragmentBound q ∧
      ts≠[] ∧ ∀t∈ts,Token S d t := by
  generalize he : Cuts.parse Cell.Cut w = pr
  obtain ⟨p,vs⟩ := pr
  have hj := Cuts.parse_join Cell.Cut w
  have hp := Cuts.parse_prefix Cell.Cut w
  have ht := Cuts.parse_intervals Cell.Cut w
  rw [he] at hj hp ht
  dsimp only at hj hp ht
  cases vs using List.reverseRecOn with
  | nil =>
    simp only [List.flatten_nil,List.append_nil] at hj
    subst w
    have hb := cut_free_fragment_bound hw (fun c hc => hp c (List.mem_of_mem_tail hc))
    change p.length≤fragmentBound q at hb
    omega
  | append_singleton ts s =>
    simp only [List.flatten_append,List.flatten_singleton] at hj
    have hs := ht s (by simp)
    have hps : Survives S d p := hw.infix ⟨[],ts.flatten++s,by simpa using hj⟩
    have hss : Survives S d s := hw.infix ⟨p++ts.flatten,[],by simpa [List.append_assoc] using hj⟩
    have hpbound : p.length≤fragmentBound q :=
      cut_free_fragment_bound hps (fun c hc => hp c (List.mem_of_mem_tail hc))
    have hsbound : s.length≤fragmentBound q := by
      obtain ⟨a,v,rfl,_,hn⟩ := hs
      exact cut_free_fragment_bound hss hn
    have hwts : Survives S d (ts.flatten++s) := hw.infix ⟨p,[],by simpa using hj⟩
    refine ⟨p,ts,s,by simpa [List.append_assoc] using hj.symm,hp,hs,hpbound,hsbound,?_,?_⟩
    · intro he
      subst ts
      have hlen := congrArg List.length hj
      simp at hlen
      omega
    · exact tokens_of_flatten hs (fun t h => ht t (List.mem_append_left _ h)) hwts
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}
lemma Survives.palette_rank_mono {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) {i j : ℕ} (hi : i<w.length) (hj : j<w.length) (hij : i ≤ j) :
    w[i].paletteRank ≤ w[j].paletteRank := by
  rcases eq_or_lt_of_le hij with rfl|hl
  · rfl
  · have hc := (hw.palette_rank_chain hp).pairwise
    have HH := List.pairwise_iff_getElem.mp hc i j (by simpa) (by simpa) hl
    simpa using HH

lemma Survives.long_equal_rank {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) (hq : 16 ≤ q) (hql : q ≤ w.length) :
    ∃v : List (Cell q), v <:+: w  ∧  2 ≤ v.length  ∧  q ≤ 100*v.length  ∧
      ∀a∈v,∀b∈v,a.paletteRank=b.paletteRank := by
  let m := max 2 ((q+99)/100)
  have hm : 2 ≤ m := le_max_left _ _
  have hqm : q ≤ 100*m := by
    have hd := Nat.mod_add_div (q+99) 100
    have hr := Nat.mod_lt (q+99) (by decide : 0<100)
    have hl := le_max_right 2 ((q+99)/100)
    dsimp [m]; omega
  have h6 : 6*m<q := by
    have hd := Nat.mod_add_div (q+99) 100
    have hl := Nat.zero_le ((q+99)%100)
    dsimp [m]
    rcases le_total 2 ((q+99)/100) with h|h
    · rw [max_eq_right h]
      omega
    · rw [max_eq_left h]
      omega
  let f : Fin 7  →  Fin 6 := fun i =>
    ⟨(w[i.val*m]'(by have := i.isLt; nlinarith)).paletteRank,Cell.paletteRank_lt _⟩
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by decide)
  have hi : i.val*m<w.length := by have := i.isLt; nlinarith
  have hj : j.val*m<w.length := by have := j.isLt; nlinarith
  have he' : (w[i.val*m]'hi).paletteRank=(w[j.val*m]'hj).paletteRank := congrArg Fin.val he
  have hab : ∃a b : ℕ, ∃(ha : a<w.length) (hb : b<w.length), a<b ∧ m ≤ b+1-a ∧
      (w[a]'ha).paletteRank=(w[b]'hb).paletteRank := by
    rcases lt_or_gt_of_ne (show i.val≠j.val from fun h => hne (Fin.ext h)) with h|h
    · refine ⟨i.val*m,j.val*m,hi,hj,by nlinarith,?_,he'⟩
      have H : i.val*m+m ≤ j.val*m := by nlinarith
      omega
    · refine ⟨j.val*m,i.val*m,hj,hi,by nlinarith,?_,he'.symm⟩
      have H : j.val*m+m ≤ i.val*m := by nlinarith
      omega
  obtain ⟨a,b,ha,hb,hab,hml,heab⟩ := hab
  let v := (w.drop a).take (b+1-a)
  have hlen : v.length=b+1-a := by simp [v,List.length_take,List.length_drop]; omega
  have hv : v <:+: w := by
    refine ⟨w.take a,(w.drop a).drop (b+1-a),?_⟩
    simp only [v,List.append_assoc,List.take_append_drop]
  refine ⟨v,hv,by omega,by nlinarith,?_⟩
  have hval : ∀c∈v,c.paletteRank=(w[a]'(by omega)).paletteRank := by
    intro c hc
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hc
    have hk' : a+k ≤ b := by rw [hlen] at hk; omega
    have hwk : a+k<w.length := by omega
    have hvk : (v[k]'hk)=(w[a+k]'hwk) := by simp [v,List.getElem_take,List.getElem_drop]
    rw [hvk]
    have h1 := hw.palette_rank_mono hp (by omega : a<w.length) hwk (by omega : a ≤ a+k)
    have h2 := hw.palette_rank_mono hp hwk hb hk'
    omega
  intro c hc e he
  exact (hval c hc).trans (hval e he).symm

lemma Survives.equal_rank_eligible {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) (hn : 2 ≤ w.length)
    (hr : ∀a∈w,∀b∈w,a.paletteRank=b.paletteRank) :
    ∃c, ∀a∈w,a.eraseColor=c  ∧  a.HeadFree := by
  have hc : w.IsChain (fun a b => a.eraseColor=b.eraseColor  ∧  a.HeadFree  ∧  b.HeadFree) :=
    hw.chain.imp_of_mem_imp (by
      intro a b ha hb hab
      exact palette_equal_rank (hp a ha) (hp b hb) (hw.format ha) (hw.format hb) hab (hr a ha b hb))
  cases w with
  | nil => simp at hn
  | cons a w =>
    cases w with
    | nil => simp at hn
    | cons b w =>
      obtain ⟨hab,ht⟩ := List.isChain_cons_cons.mp hc
      refine ⟨a.eraseColor,?_⟩
      have hh : ∀c∈b::w,c.eraseColor=a.eraseColor  ∧  c.HeadFree := by
        have hb : b.eraseColor=a.eraseColor  ∧  b.HeadFree := ⟨hab.1.symm,hab.2.2⟩
        clear hp hw hr hn hc hab
        induction w generalizing b with
        | nil => simpa using hb
        | cons c w ih =>
          obtain ⟨hbc,hw⟩ := List.isChain_cons_cons.mp ht
          intro e he
          rcases List.mem_cons.mp he with rfl|he
          · exact hb
          · exact ih c hw ⟨hbc.1.symm.trans hb.1,hbc.2.2⟩ e he
      intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact ⟨rfl,hab.2.1⟩
      · exact hh c hc

theorem Survives.palette_long_eligible {w : List (Cell q)} (hw : Survives S d w)
    (hp : ∀c∈w,c.isPalette) (hq : 16 ≤ q) (hql : q ≤ w.length) :
    ∃v : List (Cell q),v <:+: w  ∧  2 ≤ v.length  ∧  q ≤ 100*v.length  ∧
      ∃c,∀a∈v,a.isPalette  ∧  a.eraseColor=c  ∧  a.HeadFree := by
  obtain ⟨v,hv,hn,hqv,hr⟩ := hw.long_equal_rank hp hq hql
  have hpv : ∀c∈v,c.isPalette := fun c hc => hp c (hv.sublist.subset hc)
  obtain ⟨c,hc⟩ := (hw.infix hv).equal_rank_eligible hpv hn hr
  exact ⟨v,hv,hn,hqv,c,fun a ha => ⟨hpv a ha,hc a ha⟩⟩
namespace StructuralBlock
variable (B : StructuralBlock q)
lemma palette_card_le (hw : Survives S d B.word) : q ≤ B.palette.length := by
  obtain ⟨p,c,hcores,hcp⟩ := B.core_ends
  have ht : q-1+1=q := by have := NeZero.pos q; omega
  have hwpal : Survives S d (c::B.palette++[B.stop]) :=
    hw.infix ⟨p,[],by simp [word,hcores,List.append_assoc]⟩
  have hc := hwpal.palette_all_colors hcp ht B.stop_position B.palette_nonempty B.palette_positions
  have hcard : (Finset.univ : Finset (Fin q))⊆(B.palette.map Cell.color).toFinset := by
    intro x _
    exact List.mem_toFinset.mpr (hc x)
  have hl := (Finset.card_le_card hcard).trans (List.toFinset_card_le _)
  simpa using hl
end StructuralBlock
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax Cuts
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}
lemma token_contains_block {t : List (Cell q)} (ht : Token S d t) :
    ∃B : StructuralBlock q, B.word <:+: t ∧ Survives S d B.word := by
  obtain ⟨hinterval,b,hb,hw⟩ := ht
  obtain ⟨a,v,rfl,ha,_⟩ := hinterval
  have hw' : Survives S d (a::v) := hw.infix ⟨[],[b],by simp⟩
  have hstruct : StructuralChain (a::v) := hw'.chain.imp (fun _ _ h => h.1.1)
  obtain ⟨bs,he⟩ := structural_decompose (a::v) hstruct (by simpa [StartsCore] using ha.1)
    (hw.before_cut_end hb).1
  cases bs with
  | nil => simp at he
  | cons B bs =>
    have hi : B.word <:+: a::v := ⟨[],bs.flatMap StructuralBlock.word,by simpa using he.symm⟩
    exact ⟨B,hi,hw'.infix hi⟩

lemma token_long_eligible {t : List (Cell q)} (ht : Token S d t) (hq : 16 ≤ q) :
    ∃v : List (Cell q),v <:+: t ∧ 2 ≤ v.length ∧ q ≤ 100*v.length ∧
      ∃c,∀a∈v,a.isPalette ∧ a.eraseColor=c ∧ a.HeadFree := by
  obtain ⟨B,hB,hw⟩ := token_contains_block ht
  have hpal : B.palette <:+: B.word := ⟨B.cores,[B.stop],rfl⟩
  obtain ⟨v,hv,hn,hqv,hall⟩ := (hw.infix hpal).palette_long_eligible B.palette_positions hq (B.palette_card_le hw)
  exact ⟨v,hv.trans (hpal.trans hB),hn,hqv,hall⟩

theorem Survives.long_eligible {w : List (Cell q)} (hw : Survives S d w) (hq : 16 ≤ q)
    (hlong : 2*fragmentBound q<w.length) :
    ∃v : List (Cell q),v <:+: w ∧ 2 ≤ v.length ∧ q ≤ 100*v.length ∧
      ∃c,∀a∈v,a.isPalette ∧ a.eraseColor=c ∧ a.HeadFree := by
  obtain ⟨p,ts,s,he,_,_,_,_,htn,ht⟩ := hw.token_decomposition hlong
  cases ts with
  | nil => contradiction
  | cons t ts =>
    obtain ⟨v,hv,hn,hqv,hall⟩ := token_long_eligible (ht t (by simp)) hq
    have htw : t <:+: w := ⟨p,ts.flatten++s,by simpa [List.append_assoc] using he.symm⟩
    exact ⟨v,hv.trans htw,hn,hqv,hall⟩
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma Survives.has_encoding (h4 : 4 ≤ h) {w : List (Raw h)} (hw : Survives hh S d w) :
    ∃v : List (Cell (2^h)),w=v.map encode ∧ FiniteTable.Survives S d v := by
  have H : ∀a∈w,∃c : Cell (2^h),a=encode c := by
    intro a ha
    obtain ⟨p,s,he⟩ := List.mem_iff_append.mp ha
    have haz : ¬unaryZero hh S d a := by
      apply hw p [a] s
      simpa [he] using (Relation.ReflTransGen.refl : Reach hh S d w w)
    cases hc : decode hh a with
    | none => exact (haz (by simp [unaryZero,hc])).elim
    | some c => exact ⟨c,(decode_eq_some_iff h4 a c).mp hc⟩
  have Hlist : ∃v : List (Cell (2^h)),w=v.map encode := by
    clear hw
    induction w with
    | nil => exact ⟨[],rfl⟩
    | cons a w ih =>
      obtain ⟨c,rfl⟩ := H a (by simp)
      obtain ⟨v,rfl⟩ := ih (fun b hb => H b (by simp [hb]))
      exact ⟨c::v,rfl⟩
  obtain ⟨v,rfl⟩ := Hlist
  exact ⟨v,rfl,(survives_encode_iff h4 v).mp hw⟩

lemma rawCut_encode (h4 : 4 ≤ h) (c : Cell (2^h)) : rawCut hh (encode c) ↔ c.Cut := by
  simp [rawCut,decode_encode h4]

lemma fields_encode (h4 : 4 ≤ h) (c : Cell (2^h)) : fields hh (encode c)=some (noncolor c) := by
  simp [fields,decode_encode h4]
lemma erased_palette {q : ℕ} [NeZero q] (c : Cell q) (hp : c.isPalette) : c.eraseColor.isPalette := by
  obtain ⟨x,hx⟩ := hp
  exact ⟨0,rfl⟩
lemma erased_headfree {q : ℕ} [NeZero q] (c : Cell q) : c.eraseColor.HeadFree ↔ c.HeadFree := Iff.rfl
lemma Survives.long_uniform (h4 : 4 ≤ h) {w : List (Raw h)} (hw : Survives hh S d w)
    (hlong : 2*fragmentBound (2^h)<w.length) :
    ∃v : List (Raw h),v <:+: w ∧ 2 ≤ v.length ∧ 2^h ≤ 100*v.length ∧
      ∃t,eligibleFields t ∧ ∀a∈v,fields hh a=t := by
  obtain ⟨w',rfl,hw'⟩ := hw.has_encoding h4
  have hq : 16 ≤ 2^h := (show 16=2^4 from by norm_num) ▸ Nat.pow_le_pow_right (by decide) h4
  obtain ⟨v,hv,hn,hqv,c,hc⟩ := hw'.long_eligible hq (by simpa using hlong)
  have hvn : v≠[] := by intro h; simp [h] at hn
  obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil v hvn
  obtain ⟨hap,he,haf⟩ := hc a ha
  refine ⟨v.map encode,hv.map encode,by simpa,by simpa, some c,?_,?_⟩
  · exact ⟨c,rfl,he ▸ erased_palette a hap,(he ▸ (erased_headfree a).mpr haf)⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    rw [fields_encode h4,noncolor,ite_eq_left (hc a ha).1,(hc a ha).2.1]

lemma rawToken_interval (h4 : 4 ≤ h) {t : List (Raw h)} (ht : rawToken hh S d t) :
    Cuts.Interval (rawCut hh) t := by
  obtain ⟨u,hu,rfl⟩ := ht
  obtain ⟨a,v,rfl,ha,hn⟩ := hu.1
  refine ⟨encode a,v.map encode,rfl,(rawCut_encode h4 _).mpr ha,?_⟩
  intro c hc
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
  exact fun h => hn b hb ((rawCut_encode h4 _).mp h)

theorem Survives.raw_token_decomposition (h4 : 4 ≤ h) {w : List (Raw h)} (hw : Survives hh S d w)
    (hlong : 2*fragmentBound (2^h)<w.length) :
    ∃p ts s, w=p++ts.flatten++s ∧ Cuts.NoCut (rawCut hh) p ∧
      Cuts.Interval (rawCut hh) s ∧ p.length ≤ fragmentBound (2^h) ∧ s.length ≤ fragmentBound (2^h) ∧
      ts≠[] ∧ ∀t∈ts,rawToken hh S d t := by
  obtain ⟨w',rfl,hw'⟩ := hw.has_encoding h4
  obtain ⟨p,ts,s,he,hp,hs,hpB,hsB,htn,ht⟩ := hw'.token_decomposition (by simpa using hlong)
  refine ⟨p.map encode,ts.map (List.map encode),s.map encode,?_,?_,?_,by simpa,by simpa,?_,?_⟩
  · simp [he,List.map_flatten]
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact fun h => hp a ha ((rawCut_encode h4 _).mp h)
  · obtain ⟨a,v,rfl,ha,hn⟩ := hs
    refine ⟨encode a,v.map encode,rfl,(rawCut_encode h4 _).mpr ha,?_⟩
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    exact fun h => hn b hb ((rawCut_encode h4 _).mp h)
  · simpa using htn
  · intro t ht'
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht'
    exact ⟨u,ht u hu,rfl⟩
end
end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_MatrixTests
attribute [-instance] _root_.OAI.SourceBurnside.SourceMachine.MachineHierarchy.token_finite _root_.OAI.SourceBurnside.SourceMachine.MachineHierarchy.token_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
lemma embeddingHom_word (K : Type*) [CommRing K] {h : ℕ} (hh : A.threshold ≤ h) (w : List (Codec.Raw (D*h))) :
    A.embeddingHom K hh ((A.table (D*h) (A.next_large hh)).word (FreeMonoid.ofList w))=
      (A.table h hh).word (FreeMonoid.ofList (embedding h D w)) := by
  exact WordAlgebra.Table.substitution_word (K:=K) _ _ _ _ _ _
end
end SourceBurnside.SourceMachine.MachineHierarchy
namespace SourceBurnside.DirectCancellation
noncomputable section
open Classical
variable {T : Type*}

lemma maximal_of_uniform (eligible : T → Prop) (q : ℕ) {w v : List T}
    (hv : v <:+: w) (hn : 0<v.length) (hq : q ≤ 100*v.length)
    (t : T) (ht : eligible t) (hall : ∀x∈v,x=t) :
    ∃a e,EligibleInterval eligible q w a e := by
  let P : ℕ → Prop := fun n => ∃p s,w=p++List.replicate n t++s
  have hP : P v.length := by
    obtain ⟨p,s,he⟩ := hv
    exact ⟨p,s,by simpa only [←List.eq_replicate_of_mem hall] using he.symm⟩
  let n := Nat.findGreatest P w.length
  have hle : v.length ≤ n := Nat.le_findGreatest hv.length_le hP
  obtain ⟨p,s,he⟩ := Nat.findGreatest_spec hv.length_le hP
  change w=p++List.replicate n t++s at he
  have hlen : w.length=p.length+n+s.length := by simp [he,Nat.add_assoc]
  have hp : p.getLast?≠some t := by
    intro hp
    obtain ⟨a,ha⟩ := List.getLast?_eq_some_iff.mp hp
    have hP' : P (n+1) := by
      refine ⟨a,s,?_⟩
      simp only [he,ha,List.replicate_succ,List.append_assoc,List.singleton_append]
    exact Nat.findGreatest_is_greatest (show n<n+1 from Nat.lt_succ_self _) (by simp [ha] at hlen;omega) hP'
  have hs : s.head?≠some t := by
    intro hs
    obtain ⟨b,hb⟩ := List.head?_eq_some_iff.mp hs
    have hP' : P (n+1) := by
      refine ⟨p,b,?_⟩
      simp only [he,hb,List.replicate_succ',List.append_assoc,List.singleton_append]
    exact Nat.findGreatest_is_greatest (show n<n+1 from Nat.lt_succ_self _) (by simp [hb] at hlen;omega) hP'
  refine ⟨p.length,p.length+n,?_,by omega,by omega,t,ht,?_,?_,?_⟩
  · omega
  · simp [he,List.append_assoc]
  · simpa only [he,←List.append_assoc,List.take_append_of_le_length (by simp : p.length ≤ (p++List.replicate n t).length),List.take_left] using hp
  · have hh : w.drop (p.length+n)=s := by
      have hpl : (p++List.replicate n t).length=p.length+n := by simp
      rw [←hpl,he,List.drop_left]
    rwa [hh]
end
end SourceBurnside.DirectCancellation
namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
variable {K : Type*} [Ring K]
lemma eval_letter (w : List (Raw h)) :
    DirectCancellation.eval (letter (K:=K) hh S d) w =
      (algebraTable hh S d).word (FreeMonoid.ofList w) := by
  induction w with
  | nil => exact (algebraTable hh S d).word_one.symm
  | cons a w ih =>
    change letter hh S d a * DirectCancellation.eval (letter hh S d) w = _
    rw [ih]
    exact ((algebraTable hh S d).word_mul (FreeMonoid.ofList [a]) (FreeMonoid.ofList w)).symm
lemma surviving_of_eval_ne_zero (w : List (Raw h))
    (hw : DirectCancellation.eval (letter (K:=K) hh S d) w ≠ 0) : Survives hh S d w := by
  apply (survives_iff_not_vanishes w).mpr
  intro hz
  exact hw ((eval_letter w).trans ((algebraTable hh S d).word_eq_zero_of_vanishes hz))
lemma noncolor_isPalette (c : Cell (2^h)) : (noncolor c).isPalette ↔ c.isPalette := by
  unfold noncolor
  split_ifs with hc
  · exact iff_of_true (erased_palette c hc) hc
  · rfl
lemma noncolor_headFree (c : Cell (2^h)) : (noncolor c).HeadFree ↔ c.HeadFree := by
  unfold noncolor
  split_ifs <;> rfl
lemma eligible_decode {a : Raw h} (ha : eligibleFields (fields hh a)) :
    ∃c, decode hh a=some c ∧ c.isPalette ∧ c.HeadFree := by
  obtain ⟨c,he,hp,hf⟩ := ha
  cases hd : decode hh a with
  | none => simp [fields,hd] at he
  | some b =>
    have he' : noncolor b=c := by simpa [fields,hd] using he
    exact ⟨b,rfl, (noncolor_isPalette b).mp (he' ▸ hp), (noncolor_headFree b).mp (he' ▸ hf)⟩
lemma letter_commute (h4 : 4 ≤ h) (t : Option (Cell (2^h))) (ht : eligibleFields t)
    (x y : Raw h) (hx : fields hh x=t) (hy : fields hh y=t) :
    Commute (letter (K:=K) hh S d x) (letter hh S d y) := by
  by_cases hx0 : letter (K:=K) hh S d x=0
  · simp [hx0]
  by_cases hy0 : letter (K:=K) hh S d y=0
  · simp [hy0]
  obtain ⟨a,ha,hap,haf⟩ := eligible_decode (hx ▸ ht)
  obtain ⟨b,hb,hbp,hbf⟩ := eligible_decode (hy ▸ ht)
  obtain rfl := (decode_eq_some_iff h4 x a).mp ha
  obtain rfl := (decode_eq_some_iff h4 y b).mp hb
  have hfa : a.Format S d := by
    by_contra! he
    apply hx0
    apply (algebraTable hh S d).word_zero
    exact (zero_encode h4 S d _).mpr (Or.inl ⟨a,rfl,Or.inl he⟩)
  have hfb : b.Format S d := by
    by_contra! he
    apply hy0
    apply (algebraTable hh S d).word_zero
    exact (zero_encode h4 S d _).mpr (Or.inl ⟨b,rfl,Or.inl he⟩)
  have he : a.eraseColor=b.eraseColor := by
    have he' := hx.trans hy.symm
    simpa [fields_encode h4,noncolor,hap,hbp] using he'
  have hr : replacement hh S d [encode a,encode b] [encode b,encode a] := by
    exact (replacement_encode h4 S d _ _).mpr (replacement_swap_of_same_fields hap hbp hfa hfb he haf hbf)
  have he := (algebraTable hh S d).word_rep (K:=K) hr
  change letter hh S d (encode a)*letter hh S d (encode b)=_
  simpa only [letter,←WordAlgebra.Table.word_mul] using (show (algebraTable hh S d).word (K:=K) (FreeMonoid.ofList [encode a] * FreeMonoid.ofList [encode b]) = (algebraTable hh S d).word (FreeMonoid.ofList [encode b] * FreeMonoid.ofList [encode a]) from he)
lemma letter_square (h4 : 4 ≤ h) (x : Raw h) (hx : eligibleFields (fields hh x)) :
    letter (K:=K) hh S d x * letter hh S d x = 0 := by
  obtain ⟨a,ha,hap,haf⟩ := eligible_decode hx
  obtain rfl := (decode_eq_some_iff h4 x a).mp ha
  obtain ⟨c,hc⟩ := hap
  have hz : zero hh S d [encode a,encode a] :=
    (zero_encode h4 S d _).mpr (Or.inr ⟨a,a,rfl,Or.inr (Or.inl ⟨c,hc,hc⟩)⟩)
  rw [letter,←WordAlgebra.Table.word_mul]
  exact (algebraTable hh S d).word_zero (K:=K) hz
lemma long_eligible_interval (h4 : 4 ≤ h) (w : List (Raw h))
    (hn : 2*fragmentBound (2^h)+1 ≤ w.length)
    (hw : DirectCancellation.eval (letter (K:=K) hh S d) w ≠ 0) :
    ∃a e,DirectCancellation.EligibleInterval eligibleFields (2^h) (w.map (fields hh)) a e := by
  obtain ⟨v,hv,hnv,hq,t,ht,he⟩ := (surviving_of_eval_ne_zero w hw).long_uniform h4 (by omega)
  apply DirectCancellation.maximal_of_uniform eligibleFields (2^h) (hv.map (fields hh)) (by simpa using (by omega : 0<v.length)) (by simpa using hq) t ht
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  exact he a ha
end
end SourceBurnside.FiniteTable.Codec
namespace SourceBurnside.CutReduction
open scoped BigOperators
open Classical
noncomputable section
variable {α Γ R : Type*} [Fintype α] [Fintype Γ] [Semiring R]

lemma mem_candidates (n : ℕ) (s : List Γ) : s ∈ candidates Γ n ↔ s.length ≤ n := by
  simp only [candidates,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨r,f⟩,rfl⟩; simp only [List.length_ofFn]; omega
  · intro hs; exact ⟨⟨⟨s.length,by omega⟩,s.get⟩,List.ofFn_get s⟩

omit [Semiring R] [Fintype α] [Fintype Γ] in
lemma length_flatMap (token : Γ → List α) (len : Γ → ℕ) (L : ℕ)
    (hl : ∀ c, (token c).length=L*len c) (gs : List Γ) :
    (gs.flatMap token).length = L * (gs.map len).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.flatMap_cons,List.length_append,hl,ih,
      List.map_cons,List.sum_cons,Nat.mul_add]

omit [Semiring R] [Fintype α] [Fintype Γ] in
lemma length_le_sum (len : Γ → ℕ) (hl : ∀ c, 1 ≤ len c) (gs : List Γ) :
    gs.length ≤ (gs.map len).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; have := hl g; omega

omit [Fintype α] [Fintype Γ] in
lemma eval_flatMap (f : α → R) (token : Γ → List α) (gs : List Γ) :
    eval f (gs.flatMap token) = eval (fun c => eval f (token c)) gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons,eval_append,ih]
    rfl

omit [Fintype α] in
lemma mem_language (token : Γ → List α) (ps ss : Finset (List α)) (n : ℕ)
    (p s : List α) (gs : List Γ) :
    (p,s,gs) ∈ language token ps ss n ↔
      p∈ps ∧ s∈ss ∧ gs.length≤n ∧ (p++gs.flatMap token++s).length=n := by
  rw [language,Finset.mem_filter]
  simp only [Finset.product_eq_sprod,Finset.mem_product,mem_candidates,join]
  tauto

omit [Fintype α] in
lemma join_injective (cut : α → Prop) (token : Γ → List α)
    (hinj : Function.Injective token) (ht : ∀ c, Cuts.Interval cut (token c))
    (ps ss : Finset (List α)) (hp : ∀ p∈ps, Cuts.NoCut cut p)
    (hs : ∀ s∈ss, Cuts.Interval cut s) (n : ℕ) :
    Set.InjOn (join token) (language token ps ss n : Set _) := by
  rintro ⟨p,s,gs⟩ hx ⟨p',s',gs'⟩ hy he
  obtain ⟨hp0,hs0,_,_⟩ := (mem_language token ps ss n p s gs).mp hx
  obtain ⟨hp1,hs1,_,_⟩ := (mem_language token ps ss n p' s' gs').mp hy
  have ht0 : ∀ t ∈ gs.map token, Cuts.Interval cut t := by
    intro t hm; obtain ⟨g,_,rfl⟩ := List.mem_map.mp hm; exact ht g
  have ht1 : ∀ t ∈ gs'.map token, Cuts.Interval cut t := by
    intro t hm; obtain ⟨g,_,rfl⟩ := List.mem_map.mp hm; exact ht g
  have hh := Cuts.language_injective cut (hp p hp0) (hs s hs0) ht0
    (hp p' hp1) (hs s' hs1) ht1 (by simpa only [←List.flatMap_def,join] using he)
  obtain ⟨rfl,hg,rfl⟩ := hh
  have hgs : gs=gs' := (List.map_injective_iff.mpr hinj) hg
  simp only [hgs]

theorem letterSum_eq_language (cut : α → Prop) (token : Γ → List α)
    (hinj : Function.Injective token) (ht : ∀ c, Cuts.Interval cut (token c))
    (ps ss : Finset (List α)) (hp : ∀ p∈ps, Cuts.NoCut cut p)
    (hs : ∀ s∈ss, Cuts.Interval cut s) (f : α → R) (n : ℕ)
    (hcover : ∀ w, w.length=n → eval f w ≠ 0 →
      ∃ p∈ps, ∃ s∈ss, ∃ gs : List Γ, w=p++gs.flatMap token++s) :
    letterSum f n = ∑ x ∈ language token ps ss n, eval f (join token x) := by
  let W := (candidates α n).filter (fun w => w.length=n)
  let T := language token ps ss n
  have hsub : T.image (join token) ⊆ W := by
    intro w hw
    obtain ⟨⟨p,s,gs⟩,hm,rfl⟩ := Finset.mem_image.mp hw
    have hn := ((mem_language token ps ss n p s gs).mp hm).2.2.2
    exact Finset.mem_filter.mpr ⟨(mem_candidates n _).mpr (by simpa [join] using hn.le),hn⟩
  have heq : ∑ w ∈ T.image (join token), eval f w = ∑ w ∈ W, eval f w := by
    apply Finset.sum_subset hsub
    intro w hw hn
    by_contra hz
    obtain ⟨p,hp0,s,hs0,gs,hgs⟩ := hcover w (Finset.mem_filter.mp hw).2 hz
    apply hn
    apply Finset.mem_image.mpr
    refine ⟨(p,s,gs),?_,hgs.symm⟩
    apply (mem_language token ps ss n p s gs).mpr
    refine ⟨hp0,hs0,?_,by simpa only [←hgs] using (Finset.mem_filter.mp hw).2⟩
    have hpos : ∀ c, 1 ≤ (token c).length := by
      intro c; obtain ⟨a,t,he,_,_⟩ := ht c; simp [he]
    have hl := length_le_sum (fun c => (token c).length) hpos gs
    have hlen := length_flatMap token (fun c => (token c).length) 1 (by simp) gs
    rw [one_mul] at hlen
    have htot : w.length = p.length + (gs.flatMap token).length + s.length := by simp [hgs,Nat.add_assoc]
    have hw' := (Finset.mem_filter.mp hw).2
    omega
  rw [Finset.sum_image (join_injective cut token hinj ht ps ss hp hs n)] at heq
  exact heq.symm

omit [Fintype α] in

lemma slice_eq_chunk (f : α → R) (token : Γ → List α) (len : Γ → ℕ)
    (hl : ∀ c, 1 ≤ len c) (L : ℕ) (hL : 1 ≤ L)
    (hlen : ∀ c, (token c).length=L*len c) (p s : List α) (n : ℕ) :
    (∑ gs ∈ (candidates Γ n).filter
      (fun gs => (p++gs.flatMap token++s).length=n),
        eval (fun c => eval f (token c)) gs) = 0 ∨
      ∃ m, p.length+L*m+s.length=n ∧
        (∑ gs ∈ (candidates Γ n).filter
          (fun gs => (p++gs.flatMap token++s).length=n),
            eval (fun c => eval f (token c)) gs) = chunkSum len (fun c => eval f (token c)) m := by
  let T := (candidates Γ n).filter (fun gs => (p++gs.flatMap token++s).length=n)
  by_cases he : T.Nonempty
  · obtain ⟨gs,hgs⟩ := he
    let m := (gs.map len).sum
    have hn : p.length+L*m+s.length=n := by
      simpa only [List.length_append,length_flatMap token len L hlen] using
        (Finset.mem_filter.mp hgs).2
    have hmn : m ≤ n := by nlinarith
    have ht : T=(candidates Γ m).filter (fun gs => (gs.map len).sum=m) := by
      ext ts
      simp only [T,Finset.mem_filter,mem_candidates,List.length_append,
        length_flatMap token len L hlen]
      constructor
      · rintro ⟨_,he⟩
        have hm : (ts.map len).sum=m := by nlinarith
        exact ⟨by rw [←hm]; exact length_le_sum len hl ts,hm⟩
      · rintro ⟨ht,hm⟩
        exact ⟨by omega,by simpa only [hm] using hn⟩
    right
    exact ⟨m,hn,by change (∑ gs ∈ T, _) = _; rw [ht]; rfl⟩
  · left
    have ht : T=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change (∑ gs ∈ T, _) = 0
    rw [ht]; simp

theorem eventually_letterSum_zero (cut : α → Prop) (token : Γ → List α)
    (hinj : Function.Injective token) (ht : ∀ c, Cuts.Interval cut (token c))
    (ps ss : Finset (List α)) (hp : ∀ p∈ps, Cuts.NoCut cut p)
    (hs : ∀ s∈ss, Cuts.Interval cut s) (B : ℕ)
    (hpB : ∀ p∈ps, p.length ≤ B) (hsB : ∀ s∈ss, s.length ≤ B)
    (len : Γ → ℕ) (hl : ∀ c, 1 ≤ len c) (L : ℕ) (hL : 1 ≤ L)
    (hlen : ∀ c, (token c).length=L*len c) (f : α → R) (N₀ N₁ : ℕ)
    (hcover : ∀ w, N₀ ≤ w.length → eval f w ≠ 0 →
      ∃ p∈ps, ∃ s∈ss, ∃ gs : List Γ, w=p++gs.flatMap token++s)
    (hchunk : ∀ m, N₁ ≤ m → chunkSum len (fun c => eval f (token c)) m=0)
    (n : ℕ) (hn : max N₀ (2*B+L*N₁) ≤ n) : letterSum f n=0 := by
  rw [letterSum_eq_language cut token hinj ht ps ss hp hs f n
    (fun w hw h => hcover w (by omega) h)]
  rw [language,Finset.sum_filter]
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_eq_zero
  intro p hp0
  apply Finset.sum_eq_zero
  intro s hs0
  change (∑ gs ∈ candidates Γ n,
    if (p++gs.flatMap token++s).length=n then eval f (p++gs.flatMap token++s) else 0)=0
  have hslice : (∑ gs ∈ (candidates Γ n).filter
      (fun gs => (p++gs.flatMap token++s).length=n),
        eval (fun c => eval f (token c)) gs) = 0 := by
    rcases slice_eq_chunk f token len hl L hL hlen p s n with h | ⟨m,hm,he⟩
    · exact h
    · rw [he,hchunk m]
      have hp' := hpB p hp0
      have hs' := hsB s hs0
      have hn' : 2*B+L*N₁ ≤ n := by omega
      nlinarith
  have he : (∑ gs ∈ candidates Γ n,
      if (p++gs.flatMap token++s).length=n then eval f (p++gs.flatMap token++s) else 0) =
      eval f p * (∑ gs ∈ (candidates Γ n).filter
        (fun gs => (p++gs.flatMap token++s).length=n),
          eval (fun c => eval f (token c)) gs) * eval f s := by
    rw [Finset.sum_filter,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro gs _
    split_ifs <;> simp [eval_append,eval_flatMap,mul_assoc]
  rw [he,hslice,mul_zero,zero_mul]

end
end SourceBurnside.CutReduction
namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma tensor_mul (X Y : Matrix ι ι K) (a b : A) :
    tensor X a * tensor Y b = tensor (X*Y) (a*b) := by
  ext i j
  simp only [Matrix.mul_apply,tensor,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  simp [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,mul_comm]
lemma eval_tensor {α : Type*} (W : α → Matrix ι ι K) (f : α → A) (w : List α) :
    (w.map (fun a=>tensor (W a) (f a))).prod =
      tensor ((w.map W).prod) (DirectCancellation.eval f w) := by
  induction w with
  | nil => exact tensor_one.symm
  | cons a w ih =>
    simp only [List.map_cons,List.prod_cons,DirectCancellation.eval,List.map_cons,List.prod_cons] at *
    rw [ih,tensor_mul]

variable {α Γ : Type*} [Fintype α] [Fintype Γ]
omit [Fintype α] [Fintype Γ] in
lemma eval_flatMap (f : α → A) (label : Γ → List α) (gs : List Γ) :
    DirectCancellation.eval (fun c=>DirectCancellation.eval f (label c)) gs =
      DirectCancellation.eval f (gs.flatMap label) := by
  induction gs with
  | nil => rfl
  | cons a gs ih =>
    simp only [List.flatMap_cons,DirectCancellation.eval_append]
    exact congrArg (fun x=>DirectCancellation.eval f (label a)*x) ih
omit [Fintype α] in
lemma chunkSum_entry {d : ℕ} (label : Γ → List α) (W : Γ → Matrix (Fin d) (Fin d) K)
    (f : α → A) (n : ℕ) (i j : Fin d) :
    chunkSum label W f n i j = DirectCancellation.chunkSum label W f n i j := by
  unfold chunkSum CutReduction.chunkSum DirectCancellation.chunkSum
  have he : (CutReduction.candidates Γ n).filter (fun gs=>(gs.map (fun c=>(label c).length)).sum=n) =
      (DirectCancellation.candidates Γ n).filter (fun gs=>(DirectCancellation.spell label gs).length=n) := by
    apply Finset.filter_congr
    intro gs _
    simp [DirectCancellation.spell,List.length_flatMap]
  rw [he]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro gs hgs
  have hh := congrArg (fun M : Matrix (Fin d) (Fin d) A=>M i j) (eval_tensor W (fun c=>DirectCancellation.eval f (label c)) gs)
  simpa only [CutReduction.eval,eval_flatMap,tensor,Cancellation.chunkWeight,DirectCancellation.spell] using hh
omit [Fintype α] in
lemma direct_vanish {T : Type*} [CharP K 2] {d b q N : ℕ}
    (label : Γ → List α) (hne : ∀c,label c≠[]) (hb : ∀c,(label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀t,eligible t → ∀x y,erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀x,eligible (erase x) → f x*f x=0)
    (hlong : ∀w : List α,N ≤ w.length → DirectCancellation.eval f w≠0 →
      ∃a e,DirectCancellation.EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*(d^2+3)<q) (W : Γ → Matrix (Fin d) (Fin d) K) :
    ∀n,N ≤ n → chunkSum label W f n=0 := by
  intro n hn
  ext i j
  rw [chunkSum_entry]
  exact DirectCancellation.direct_cancellation label hne hb erase eligible f hcomm hsquare hlong hbound W n hn i j
end
end SourceBurnside.MatrixTests
namespace SourceBurnside.CutReduction
noncomputable section
open Classical
open scoped BigOperators
variable {α R : Type*} [Fintype α] [Semiring R]
lemma letterSum_eq_ofFn (f : α → R) (n : ℕ) :
    letterSum f n=∑ w : Fin n → α,eval f (List.ofFn w) := by
  have he : (candidates α n).filter (fun w=>w.length=n)=Finset.univ.image (fun w : Fin n→α=>List.ofFn w) := by
    ext w
    simp only [Finset.mem_filter,mem_candidates,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,hw⟩
      subst n
      exact ⟨w.get,List.ofFn_get w⟩
    · rintro ⟨v,rfl⟩
      simp
  rw [letterSum,he,Finset.sum_image]
  exact fun _ _ _ _ h=>List.ofFn_injective h
end
end SourceBurnside.CutReduction
namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {ι : Type*} [Fintype ι] [decι : DecidableEq ι]
variable {α Γ : Type*} [Fintype α] [Fintype Γ]
omit [Fintype ι] decι in
lemma tensor_left_zero (a : A) : tensor (0:Matrix ι ι K) a=0 := by ext;simp [tensor]
omit [Fintype ι] decι in
lemma tensor_sum {J : Type*} (s : Finset J) (W : J → Matrix ι ι K) (a : A) :
    tensor (∑j∈s,W j) a=∑j∈s,tensor (W j) a := by
  ext i j
  simp [tensor,Matrix.sum_apply,Finset.sum_smul]
omit [Fintype Γ] in
lemma bounded_list_injective (n : ℕ) :
    Function.Injective (fun s : Automaton.BoundedSequences Γ n=>List.ofFn s.2) := by
  rintro ⟨⟨i,hi⟩,f⟩ ⟨⟨j,hj⟩,g⟩ he
  have hij : i=j := by simpa using congrArg List.length he
  subst j
  have hfg : f=g := List.ofFn_injective he
  subst g
  rfl
omit [Fintype α] in
lemma chunkSum_eq_sequences (label : Γ → List α) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) :
    chunkSum label W f n=∑s : Automaton.BoundedSequences Γ n,
      if (Automaton.spelled label s).length=n then
        tensor (Automaton.seqWeight W s) (DirectCancellation.eval f (Automaton.spelled label s)) else 0 := by
  unfold chunkSum CutReduction.chunkSum
  rw [Finset.sum_filter,CutReduction.candidates,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s _
    have hl : ((List.ofFn s.2).map (fun c=>(label c).length)).sum=(Automaton.spelled label s).length := by
      simp [Automaton.spelled,List.length_flatten,List.map_ofFn,Function.comp_def]
    rw [hl]
    split_ifs <;> try rfl
    change ((List.ofFn s.2).map (fun c=>tensor (W c) (DirectCancellation.eval f (label c)))).prod=_
    rw [eval_tensor,eval_flatMap]
    simp only [Automaton.seqWeight,Automaton.spelled,List.map_ofFn,List.flatMap]
  · exact fun _ _ _ _ he=>bounded_list_injective n he
lemma sum_wordCoefficient_tensor (label : Γ → List α) (W : Γ → Matrix ι ι K)
    (f : α → A) (n : ℕ) :
    (∑w : Fin n → α,tensor (Automaton.wordCoefficient label W (List.ofFn w))
      (DirectCancellation.eval f (List.ofFn w)))=chunkSum label W f n := by
  have hc (w : Fin n→α) : Automaton.wordCoefficient label W (List.ofFn w)=
      ∑s : Automaton.BoundedSequences Γ n,if Automaton.spelled label s=List.ofFn w then Automaton.seqWeight W s else 0 := by
    have aux (v : List α) (m : ℕ) (hm : v.length=m) : Automaton.wordCoefficient label W v=
        ∑s : Automaton.BoundedSequences Γ m,if Automaton.spelled label s=v then Automaton.seqWeight W s else 0 := by
      subst m
      rfl
    exact aux _ _ List.length_ofFn
  simp_rw [hc,tensor_sum]
  rw [Finset.sum_comm,chunkSum_eq_sequences]
  apply Finset.sum_congr rfl
  intro s _
  have he (w : Fin n→α) : tensor (if Automaton.spelled label s=List.ofFn w then Automaton.seqWeight W s else 0)
      (DirectCancellation.eval f (List.ofFn w)) =
      if List.ofFn w=Automaton.spelled label s then tensor (Automaton.seqWeight W s)
        (DirectCancellation.eval f (Automaton.spelled label s)) else 0 := by
    split_ifs <;> simp_all [tensor_left_zero]
  simp_rw [he]
  exact Automaton.sum_words_eq (Automaton.spelled label s) n _

lemma automaton_block {b : ℕ} (hb : 0<b) (label : Γ → List α) (hne : ∀c,label c≠[])
    (hl : ∀c,(label c).length ≤ b) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) (i j : ι) :
    letterSum (Automaton.blockTransition (b:=b) (Automaton.combinedWeight label W)) f n (Automaton.root hb,i) (Automaton.root hb,j)=
      chunkSum label W f n i j := by
  have he := congrArg (fun M : Matrix ι ι A=>M i j) (sum_wordCoefficient_tensor label W f n)
  rw [letterSum,CutReduction.letterSum_eq_ofFn]
  simp only [CutReduction.eval,eval_tensor,Matrix.sum_apply,tensor] at *
  apply Eq.trans ?_ he
  apply Finset.sum_congr rfl
  intro w _
  have hdec : decι = Classical.decEq ι := Subsingleton.elim _ _
  subst decι
  exact congrArg (fun c : K=>c • DirectCancellation.eval f (List.ofFn w)) (Automaton.root_block_eq_wordCoefficient hb label hne hl W (List.ofFn w) i j)
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
omit decι [DecidableEq κ] in
lemma reindex_tensor (e : ι ≃ κ) (W : Matrix ι ι K) (a : A) :
    Matrix.reindexRingEquiv A e (tensor W a)=tensor (Matrix.reindexRingEquiv K e W) a := rfl
omit [Fintype α] in
lemma reindex_chunkSum (e : ι ≃ κ) (label : Γ → List α) (W : Γ → Matrix ι ι K) (f : α → A) (n : ℕ) :
    Matrix.reindexRingEquiv A e (chunkSum label W f n)=chunkSum label (fun c=>Matrix.reindexRingEquiv K e (W c)) f n := by
  simp only [chunkSum,CutReduction.chunkSum,CutReduction.eval,map_sum,map_list_prod,List.map_map,Function.comp_def,reindex_tensor]
omit [Fintype α] in
lemma direct_vanish_finite {T : Type*} [CharP K 2] {b q N : ℕ}
    (label : Γ → List α) (hne : ∀c,label c≠[]) (hb : ∀c,(label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀t,eligible t → ∀x y,erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀x,eligible (erase x) → f x*f x=0)
    (hlong : ∀w : List α,N ≤ w.length → DirectCancellation.eval f w≠0 →
      ∃a e,DirectCancellation.EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*((Fintype.card ι)^2+3)<q) (W : Γ → Matrix ι ι K) :
    ∀n,N ≤ n → chunkSum label W f n=0 := by
  intro n hn
  apply (Matrix.reindexRingEquiv A (Fintype.equivFin ι)).injective
  rw [map_zero,reindex_chunkSum]
  exact direct_vanish label hne hb erase eligible f hcomm hsquare hlong hbound _ n hn
end
end SourceBurnside.MatrixTests

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_PresentationModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)
lemma normal_spec (t : A.Token hh) :
    1 ≤ (A.normal hh t).length ∧ (A.normal hh t).length ≤ 10 ∧
      t.val.length=(2*(2^h)+1)*(A.normal hh t).length ∧
      Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) t.val (embedding h D (A.normal hh t)) :=
  Classical.choose_spec (Codec.rawToken_normalize (A.threshold_four.trans hh) (A.fits h hh).2.2.2.1 t.property)
lemma normal_word (K : Type*) [CommRing K] (t : A.Token hh) :
    (A.table h hh).word (K:=K) (FreeMonoid.ofList t.val)=
      A.embeddingHom K hh ((A.table (D*h) (A.next_large hh)).word (FreeMonoid.ofList (A.normal hh t))) := by
  rw [A.embeddingHom_word]
  exact (A.table h hh).word_reach (Codec.reach_iff_table.mp (A.normal_spec hh t).2.2.2)
lemma eval_letters (K : Type*) [CommRing K] (w : List (Codec.Raw h)) :
    DirectCancellation.eval (A.letters hh K) w=(A.table h hh).word (FreeMonoid.ofList w) :=
  Codec.eval_letter w

theorem cut_reduction (K : Type*) [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Codec.Raw h → Matrix ι ι K)
    (H : ∀W' : A.Token hh → Matrix ι ι K, ∃N,∀n,N ≤ n →
      MatrixTests.chunkSum (A.normal hh) W' (A.letters (A.next_large hh) K) n=0) :
    ∃N,∀n,N ≤ n → MatrixTests.letterSum W (A.letters hh K) n=0 := by
  let f : Codec.Raw h → Matrix ι ι (A.Algebra K h hh) := fun a=>MatrixTests.tensor (W a) (A.letters hh K a)
  let B := fragmentBound (2^h)
  let ps := (CutReduction.candidates (Codec.Raw h) B).filter (Cuts.NoCut (Codec.rawCut (A.height_pos hh)))
  let ss := (CutReduction.candidates (Codec.Raw h) B).filter (Cuts.Interval (Codec.rawCut (A.height_pos hh)))
  let token : A.Token hh → List (Codec.Raw h) := Subtype.val
  let len : A.Token hh → ℕ := fun t=>(A.normal hh t).length
  let W' : A.Token hh → Matrix ι ι K := fun t=>(t.val.map W).prod
  obtain ⟨N,hN⟩ := H W'
  let E : Matrix ι ι (A.Algebra K (D*h) (A.next_large hh)) →ₐ[K] Matrix ι ι (A.Algebra K h hh) :=
    (A.embeddingHom K hh).mapMatrix
  have ht : ∀t, E (MatrixTests.tensor (W' t) (DirectCancellation.eval (A.letters (A.next_large hh) K) (A.normal hh t))) =
      CutReduction.eval f (token t) := by
    intro t
    change _=(t.val.map (fun a=>MatrixTests.tensor (W a) (A.letters hh K a))).prod
    rw [MatrixTests.eval_tensor,A.eval_letters,A.eval_letters]
    ext i j
    change A.embeddingHom K hh (W' t i j • (A.table (D*h) (A.next_large hh)).word (FreeMonoid.ofList (A.normal hh t)))=_
    rw [map_smul,←A.normal_word]
    rfl
  have hchunk : ∀m,N ≤ m → CutReduction.chunkSum len (fun t=>CutReduction.eval f (token t)) m=0 := by
    intro m hm
    have he := congrArg E (hN m hm)
    rw [map_zero] at he
    change E (CutReduction.chunkSum len (fun t=>MatrixTests.tensor (W' t) (DirectCancellation.eval (A.letters (A.next_large hh) K) (A.normal hh t))) m)=0 at he
    simpa only [CutReduction.chunkSum,CutReduction.eval,map_sum,map_list_prod,List.map_map,Function.comp_def,ht] using he
  have hcover : ∀w,2*B+1 ≤ w.length → CutReduction.eval f w≠0 →
      ∃p∈ps,∃s∈ss,∃gs : List (A.Token hh),w=p++gs.flatMap token++s := by
    intro w hwn hwe
    have hw : Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) w := by
      apply Codec.surviving_of_eval_ne_zero (K:=K) w
      intro hz
      apply hwe
      change (w.map (fun a=>MatrixTests.tensor (W a) (A.letters hh K a))).prod=0
      rw [MatrixTests.eval_tensor]
      rw [show DirectCancellation.eval (A.letters hh K) w=0 from hz,MatrixTests.tensor_zero]
    obtain ⟨p,ts,s,he,hp,hs,hpB,hsB,htn,htt⟩ := hw.raw_token_decomposition (A.threshold_four.trans hh) (by omega)
    have lift : ∃gs : List (A.Token hh),gs.map token=ts := by
      clear he hw hwn hwe htn
      induction ts with
      | nil => exact ⟨[],rfl⟩
      | cons t ts ih =>
        obtain ⟨gs,rfl⟩ := ih (fun u hu=>htt u (by simp [hu]))
        exact ⟨⟨t,htt t (by simp)⟩::gs,rfl⟩
    obtain ⟨gs,hgs⟩ := lift
    refine ⟨p,Finset.mem_filter.mpr ⟨(CutReduction.mem_candidates _ _).mpr hpB,hp⟩,
      s,Finset.mem_filter.mpr ⟨(CutReduction.mem_candidates _ _).mpr hsB,hs⟩,gs,?_⟩
    rw [←hgs] at he
    simpa only [List.flatMap] using he
  refine ⟨max (2*B+1) (2*B+(2*(2^h)+1)*N),fun n hn=>?_⟩
  exact CutReduction.eventually_letterSum_zero (Codec.rawCut (A.height_pos hh)) token
    Subtype.val_injective (fun t=>Codec.rawToken_interval (A.threshold_four.trans hh) t.property)
    ps ss (fun _ hp=>(Finset.mem_filter.mp hp).2) (fun _ hs=>(Finset.mem_filter.mp hs).2) B
    (fun _ hp=>(CutReduction.mem_candidates _ _).mp (Finset.mem_filter.mp hp).1)
    (fun _ hs=>(CutReduction.mem_candidates _ _).mp (Finset.mem_filter.mp hs).1)
    len (fun t=>(A.normal_spec hh t).1) (2*(2^h)+1) (by omega)
    (fun t=>(A.normal_spec hh t).2.2.1) f (2*B+1) N hcover hchunk n hn
end
end SourceBurnside.SourceMachine.MachineHierarchy
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type*) [CommRing K]

lemma cut_step {d : ℕ} (H : A.ChunkVanish (A.next_large hh) K d 10) : A.LetterVanish hh K d := by
  intro ι _ _ hid W
  apply A.cut_reduction hh K W
  intro W'
  exact H ι (A.Token hh) hid (A.normal hh)
    (fun t=>List.ne_nil_of_length_pos (A.normal_spec hh t).1)
    (fun t=>(A.normal_spec hh t).2.1) W'
lemma automaton_step {d b : ℕ} (hb : 0<b)
    (H : A.LetterVanish hh K (b*(Fintype.card (Codec.Raw h))^b*d)) : A.ChunkVanish hh K d b := by
  intro ι Γ _ _ _ hid label hne hl W
  let : DecidableEq (Codec.Raw h) := Classical.decEq _
  let V := Automaton.blockTransition (b:=b) (Automaton.combinedWeight label W)
  have hcard : Fintype.card (Automaton.State (Codec.Raw h) b × ι) ≤ b*(Fintype.card (Codec.Raw h))^b*d := by
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul (Automaton.card_state b) hid
  obtain ⟨N,hN⟩ := H (Automaton.State (Codec.Raw h) b × ι) hcard V
  refine ⟨N,fun n hn=>?_⟩
  ext i j
  rw [←MatrixTests.automaton_block hb label hne hl W (A.letters hh K) n i j]
  change MatrixTests.letterSum V (A.letters hh K) n _ _=0
  rw [hN n hn]
  rfl
lemma direct_step [CharP K 2] {d b : ℕ} (hb : 100*b*(d^2+3)<2^h) : A.ChunkVanish hh K d b := by
  intro ι Γ _ _ _ hid label hne hl W
  refine ⟨2*fragmentBound (2^h)+1,?_⟩
  apply MatrixTests.direct_vanish_finite label hne hl (Codec.fields (A.height_pos hh)) Codec.eligibleFields (A.letters hh K)
  · exact Codec.letter_commute (A.threshold_four.trans hh)
  · exact Codec.letter_square (A.threshold_four.trans hh)
  · exact Codec.long_eligible_interval (A.threshold_four.trans hh)
  · exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left hid 2) 3)) hb

theorem all_letter_tests [CharP K 2] (hDbig : 10*(10000+1)*(10+1)<D) (d : ℕ) :
    A.LetterVanish hh K d := by
  let H := D*h
  let size : ℕ → ℕ := fun n=>Fintype.card (Codec.Raw (HierarchyGrowth.height H D n))
  let dim : ℕ → ℕ := HierarchyGrowth.dimension (max 1 d) 10 size
  have hH : 1 ≤ H := Nat.mul_pos (by omega) (A.height_pos hh)
  have hs (n : ℕ) : size n ≤ 2^(10000*HierarchyGrowth.height H D n) := by
    simp [size,Codec.Raw,Fintype.card_fin]
  have hsize (n : ℕ) : 1 ≤ size n := Fintype.card_pos
  have hdim (n : ℕ) : 1 ≤ dim n := by
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      change 1 ≤ 10*(size n)^10*dim n
      have hs : 0 < (size n)^10 := Nat.pow_pos (hsize n)
      nlinarith
  have hlarge (n : ℕ) : A.threshold ≤ HierarchyGrowth.height H D n := by
    have hn : 1 ≤ D^n := Nat.one_le_pow n D (by omega)
    have hh' := A.next_large hh
    change A.threshold ≤ H*D^n
    exact hh'.trans (Nat.le_mul_of_pos_right H hn)
  obtain ⟨N,hN⟩ := HierarchyGrowth.stopping_index H D (max 1 d) 10 10000 size hH hDbig hs
  have hlast : A.ChunkVanish (hlarge N) K (dim N) 10 := by
    apply A.direct_step (hlarge N) K
    have hd := hdim N
    change 400*10*(dim N)^2 < 2^HierarchyGrowth.height H D N at hN
    nlinarith [Nat.one_le_iff_ne_zero.mpr (by omega : dim N≠0)]
  have hstep (i : ℕ) (Hup : A.ChunkVanish (hlarge (i+1)) K (dim (i+1)) 10) :
      A.ChunkVanish (hlarge i) K (dim i) 10 := by
    apply A.automaton_step (hlarge i) K (by decide : 0<10)
    apply A.cut_step (hlarge i) K
    simpa only [HierarchyGrowth.height_succ,dim,HierarchyGrowth.dimension,size] using Hup
  have hfirst : A.ChunkVanish (hlarge 0) K (dim 0) 10 := by
    exact Nat.decreasingInduction (motive := fun i _ => A.ChunkVanish (hlarge i) K (dim i) 10) (fun i _ hi' => hstep i hi') hlast (Nat.zero_le N)
  have hlower : A.LetterVanish hh K (max 1 d) := by
    apply A.cut_step hh K
    simpa only [HierarchyGrowth.height,pow_zero,mul_one,dim,HierarchyGrowth.dimension,H] using hfirst
  intro ι _ _ hi W
  exact hlower ι (hi.trans (le_max_right _ _)) W
theorem all_chunk_tests [CharP K 2] (hDbig : 10*(10000+1)*(10+1)<D) (d b : ℕ) (hb : 0<b) :
    A.ChunkVanish hh K d b :=
  A.automaton_step hh K hb (A.all_letter_tests hh K hDbig _)
end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
variable {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]

lemma polynomialMatrix_coeff (p : Polynomial (Matrix ι ι A)) (n : ℕ) (i j : ι) :
    (polynomialMatrix p i j).coeff n=p.coeff n i j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Matrix.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial m a =>
    rw [polynomialMatrix_monomial]
    simp only [Polynomial.coeff_monomial]
    split_ifs <;> rfl
lemma polynomialMatrix_injective : Function.Injective (polynomialMatrix (A:=A) (ι:=ι)) := by
  intro p q hpq
  ext n i j
  simpa only [←polynomialMatrix_coeff] using congrArg (fun M : Matrix ι ι (Polynomial A)=>(M i j).coeff n) hpq
end
end SourceBurnside.MatrixTests

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {Γ R : Type*} [Fintype Γ] [Semiring R]
omit [Fintype Γ] in
lemma eval_monomial_one (f : Γ → R) (v : List Γ) :
    CutReduction.eval (fun c=>Polynomial.monomial 1 (f c)) v=
      Polynomial.monomial v.length (CutReduction.eval f v) := by
  induction v with
  | nil => simp [CutReduction.eval]
  | cons c v ih =>
    change Polynomial.monomial 1 (f c)*CutReduction.eval (fun c=>Polynomial.monomial 1 (f c)) v=_
    rw [ih,Polynomial.monomial_mul_monomial]
    simp [CutReduction.eval,Nat.add_comm]

lemma chunkSum_monomial (len : Γ → ℕ) (f : Γ → R) (n : ℕ) :
    CutReduction.chunkSum len (fun c=>Polynomial.monomial 1 (f c)) n=
      WeightedTests.lengthPolynomial len f n := by
  unfold CutReduction.chunkSum
  rw [Finset.sum_filter,CutReduction.candidates,Finset.sum_image]
  · simp_rw [eval_monomial_one]
    rw [Fintype.sum_sigma]
    simp only [List.length_ofFn,CutReduction.eval,List.map_ofFn,List.sum_ofFn]
    change (∑r : Fin (n+1),∑v : Fin r.val→Γ,
      if WeightedTests.length len v=n then Polynomial.monomial r.val (WeightedTests.product f v) else 0)=_
    exact Fin.sum_univ_eq_sum_range (fun r=>∑v : Fin r→Γ, if WeightedTests.length len v=n then Polynomial.monomial r (WeightedTests.product f v) else 0) (n+1)
  · exact fun _ _ _ _ h=>bounded_list_injective n h
end
end SourceBurnside.MatrixTests

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A B ι : Type*} [CommRing K] [Ring A] [Ring B] [Algebra K A]
variable [Algebra (Polynomial K) B] [Fintype ι] [DecidableEq ι]
attribute [local instance] OAI.SourceBurnside.MatrixTests.instAlgebraPolynomial_solutions
lemma polynomial_tensor (F : B →ₐ[Polynomial K] Polynomial A)
    (x : B) (a : A) (hx : F x=Polynomial.C a) (W : Matrix ι ι K) :
    F.mapMatrix (tensor (fun i j=>Polynomial.monomial 1 (W i j)) x)=
      polynomialMatrix (Polynomial.monomial 1 (tensor W a)) := by
  apply Matrix.ext
  intro i j
  change F (Polynomial.monomial 1 (W i j) • x)=_
  rw [map_smul,hx,polynomialMatrix_monomial]
  change Polynomial.monomial 1 (W i j) • Polynomial.C a=
    Polynomial.monomial 1 (W i j • a)
  rw [Algebra.smul_def,Polynomial.algebraMap_def]
  change Polynomial.map (algebraMap K A) (Polynomial.monomial 1 (W i j))*Polynomial.C a=_
  rw [Polynomial.map_monomial]
  change Polynomial.monomial 1 ((algebraMap K A) (W i j))*Polynomial.monomial 0 a=_
  rw [Polynomial.monomial_mul_monomial]
  simp only [Nat.add_zero,Algebra.smul_def]
variable {Γ R S : Type*} [Fintype Γ] [Semiring R] [Semiring S]
lemma map_chunkSum (F : R →+* S) (len : Γ → ℕ) (f : Γ → R) (n : ℕ) :
    F (CutReduction.chunkSum len f n)=CutReduction.chunkSum len (fun c=>F (f c)) n := by
  simp only [CutReduction.chunkSum,CutReduction.eval,map_sum,map_list_prod,List.map_map,Function.comp_def]

lemma map_test_polynomial {α : Type*} [Fintype α]
    (F : B →ₐ[Polynomial K] Polynomial A) (f : α → B) (g : α → A)
    (hf : ∀v : List α,F (DirectCancellation.eval f v)=Polynomial.C (DirectCancellation.eval g v))
    (label : Γ → List α) (W : Γ → Matrix ι ι K) (n : ℕ) :
    F.mapMatrix (chunkSum label (fun c i j=>Polynomial.monomial 1 (W c i j)) f n)=
      polynomialMatrix (WeightedTests.lengthPolynomial (fun c=>(label c).length)
        (fun c=>tensor (W c) (DirectCancellation.eval g (label c))) n) := by
  let l : Γ → ℕ := fun c=>(label c).length
  let t : Γ → Matrix ι ι A := fun c=>tensor (W c) (DirectCancellation.eval g (label c))
  let tp : Γ → Matrix ι ι B := fun c=>tensor (fun i j=>Polynomial.monomial 1 (W c i j)) (DirectCancellation.eval f (label c))
  change F.toRingHom.mapMatrix (CutReduction.chunkSum l tp n)=polynomialMatrix (WeightedTests.lengthPolynomial l t n)
  have ht : (fun c=>F.toRingHom.mapMatrix (tp c))=(fun c=>polynomialMatrix (Polynomial.monomial 1 (t c))) := by
    funext c
    exact polynomial_tensor F _ _ (hf (label c)) (W c)
  exact (map_chunkSum F.toRingHom.mapMatrix l tp n).trans
    ((congrArg (fun w=>CutReduction.chunkSum l w n) ht).trans
      ((map_chunkSum polynomialMatrix l (fun c=>Polynomial.monomial 1 (t c)) n).symm.trans
        (congrArg polynomialMatrix (chunkSum_monomial l t n))))
end
end SourceBurnside.MatrixTests

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type) [CommRing K] [CharP K 2]
variable {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Fintype Γ]

theorem word_matrix_sum_nilpotent (hDbig : 10*(10000+1)*(10+1)<D)
    (label : Γ → List (Codec.Raw h)) (hne : ∀c,label c≠[]) (W : Γ → Matrix ι ι K) :
    IsNilpotent (∑c,MatrixTests.tensor (W c) (DirectCancellation.eval (A.letters hh K) (label c))) := by
  let : _root_.Algebra (Polynomial K) (Polynomial (A.Algebra K h hh)) := Polynomial.algebra K _
  let F := (A.table h hh).polynomialCoefficients (K:=K)
  have hF : ∀v : List (Codec.Raw h),F (DirectCancellation.eval (A.letters hh (Polynomial K)) v)=
      Polynomial.C (DirectCancellation.eval (A.letters hh K) v) := by
    intro v
    rw [A.eval_letters,A.eval_letters]
    exact WordAlgebra.Table.polynomialCoefficients_word _ _
  let b : ℕ := 1+∑c,(label c).length
  have hb : 0<b := by dsimp [b];omega
  have hl : ∀c,(label c).length ≤ b := by
    intro c
    have hc := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset Γ))=>Nat.zero_le ((label i).length)) (Finset.mem_univ c)
    exact hc.trans (by dsimp [b];omega)
  let P : Γ → Matrix ι ι (Polynomial K) := fun c i j=>Polynomial.monomial 1 (W c i j)
  obtain ⟨N,hN⟩ := A.all_chunk_tests hh (Polynomial K) hDbig (Fintype.card ι) b hb
    ι Γ le_rfl label hne hl P
  apply WeightedTests.nilpotent_of_eventually_zero_lengthPolynomial (fun c=>(label c).length)
    (fun c=>List.length_pos_iff.mpr (hne c))
  refine ⟨N,fun n hn=>?_⟩
  apply MatrixTests.polynomialMatrix_injective
  rw [map_zero]
  have he := MatrixTests.map_test_polynomial F (A.letters hh (Polynomial K)) (A.letters hh K) hF label W n
  exact he.symm.trans ((congrArg F.mapMatrix (hN n hn)).trans (map_zero _))
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type) [CommRing K]

variable [CharP K 2]

theorem positive_matrix_nilpotent (hDbig : 10*(10000+1)*(10+1)<D)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (A.Algebra K h hh))
    (hM : ∀i j,M i j∈A.positiveSpan hh K) : IsNilpotent M := by
  let P := {w : List (Codec.Raw h) // w≠[]}
  have H (i j : ι) : ∃p : P →₀ K,
      p.sum (fun w a=>a • DirectCancellation.eval (A.letters hh K) w.val)=M i j :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hM i j)
  choose p hp using H
  let Γ := Σi : ι,Σj : ι,{w : P // w∈(p i j).support}
  let label : Γ → List (Codec.Raw h) := fun c=>c.2.2.val.val
  let W : Γ → Matrix ι ι K := fun c=>Matrix.single c.1 c.2.1 (p c.1 c.2.1 c.2.2.val)
  have hz (w : P) : (0:K) • DirectCancellation.eval (A.letters hh K) w.val=0 := by
    exact @zero_smul K (A.Algebra K h hh) inferInstance inferInstance inferInstance _
  have he : (∑c : Γ,MatrixTests.tensor (W c) (DirectCancellation.eval (A.letters hh K) (label c)))=M := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sum_apply,Γ,Fintype.sum_sigma,MatrixTests.tensor,W,label,Matrix.single_apply]
    simp only [ite_smul,ite_and,hz,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact (Finset.sum_coe_sort (p i j).support
      (fun w : P=>(p i j) w • DirectCancellation.eval (A.letters hh K) w.val)).trans (hp i j)
  rw [←he]
  exact A.word_matrix_sum_nilpotent hh K hDbig label (fun c=>c.2.2.val.property) W
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α K : Type*} [CommRing K]
lemma quotient_smul (T : Table α) (k : K) (p : Polynomial K α) : T.quotient (k • p)=k • T.quotient p :=
  map_smul (RingCon.mkₐ K (T.ideal (K:=K)).ringCon) k p

lemma sub_augmentation_mem (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1)
    (P : Submodule K (T.Algebra (K:=K))) (hpos : ∀w : FreeMonoid α,w≠1 → T.word w∈P)
    (x : T.Algebra (K:=K)) : x-algebraMap K _ (T.augmentation hh hz x)∈P := by
  obtain ⟨p,rfl⟩ := (T.ideal (K:=K)).ringCon.mk'_surjective x
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change T.word w-algebraMap K _ (T.augmentation hh hz (T.word w))∈P
    by_cases hw : w=1
    · simp [hw]
    · rw [augmentation_word,ite_eq_right (fun h=>hw (FreeMonoid.length_eq_zero.mp h)),map_zero,sub_zero]
      exact hpos w hw
  | add p q hp hq =>
    have he : T.quotient (p+q)-algebraMap K _ (T.augmentation hh hz (T.quotient (p+q)))=
        (T.quotient p-algebraMap K _ (T.augmentation hh hz (T.quotient p)))+
        (T.quotient q-algebraMap K _ (T.augmentation hh hz (T.quotient q))) := by
      simp only [map_add]
      abel
    rw [he]
    exact P.add_mem hp hq
  | smul k p hp =>
    rw [quotient_smul,map_smul,smul_eq_mul,map_mul,←Algebra.smul_def,←smul_sub]
    exact P.smul_mem k hp
lemma kernel_mem (T : Table α) (hh : T.Homogeneous) (hz : ∀z∈T.zero,z≠1)
    (P : Submodule K (T.Algebra (K:=K))) (hpos : ∀w : FreeMonoid α,w≠1 → T.word w∈P)
    (x : T.Algebra (K:=K)) (hx : T.augmentation hh hz x=0) : x∈P := by
  have H := sub_augmentation_mem T hh hz P hpos x
  simpa only [hx,map_zero,sub_zero] using H
end
end SourceBurnside.WordAlgebra.Table

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)
lemma augmentation_kernel_positive (K : Type) [CommRing K] (x : A.Algebra K h hh)
    (hx : A.augmentation hh K x=0) : x∈A.positiveSpan hh K := by
  apply (A.table h hh).kernel_mem (A.table_homogeneous hh) (A.table_zero_nonempty hh) _ _ x hx
  intro w hw
  apply Submodule.subset_span
  refine ⟨⟨w.toList,?_⟩,?_⟩
  · intro he
    apply hw
    simpa using congrArg FreeMonoid.ofList he
  · exact A.eval_letters hh K w.toList

theorem matrixNilKernel_oai (hDbig : 10*(10000+1)*(10+1)<D) :
    MatrixNilKernel (A.augmentation hh (ZMod 2)).toRingHom := by
  intro n M hM
  apply A.positive_matrix_nilpotent hh (ZMod 2) hDbig M
  intro i j
  exact A.augmentation_kernel_positive hh (ZMod 2) (M i j) (hM i j)

end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end

theorem solution : type_of% @OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel_oai := @OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel_oai
