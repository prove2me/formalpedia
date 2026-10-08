-- Prove2me | solution 1 for OAI.TorsionFreeZeroDivisors.BoundedPattern.probability_union
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:31:36.183961+00:00
-- url     : https://prove2.me/submissions/3949aae6-07ea-4080-88e4-a9d673cec5aa

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BlockGrid

end TorsionFreeZeroDivisors.BlockGrid

/-! Exact half-integer alignment, including the reflection endpoint conventions.
Uniform deficit bounds converge to zero relative to s
when |a/s-ν| does; no rounding of the prescribed real grid s is needed. -/
namespace TorsionFreeZeroDivisors.BlockAlignment

section
open scoped Classical

/-- Works even for a reversed/empty real interval. -/
theorem card_lower (lo hi : ℝ) : hi-lo-1 ≤ ((positions lo hi).card : ℝ) := by
  have h1 := Int.le_ceil (lo-1/2)
  have h2 := Int.ceil_lt_add_one (lo-1/2)
  have h3 := Int.le_ceil (hi-1/2)
  have h4 : (⌈hi-1/2⌉-⌈lo-1/2⌉ : ℤ) ≤ ((positions lo hi).card : ℤ) := by
    simp only [positions,Int.card_Ico]
    exact Int.self_le_toNat _
  have h5 : ((⌈hi-1/2⌉ : ℤ) : ℝ)-⌈lo-1/2⌉ ≤ ((positions lo hi).card : ℝ) := by exact_mod_cast h4
  linarith

theorem card_upper {lo hi : ℝ} (hab : lo ≤ hi) :
    ((positions lo hi).card : ℝ) ≤ hi-lo+1 := by
  have hc : ⌈lo-1/2⌉ ≤ ⌈hi-1/2⌉ := Int.ceil_mono (by linarith)
  have he : ((positions lo hi).card : ℤ) = ⌈hi-1/2⌉-⌈lo-1/2⌉ := by
    simp only [positions,Int.card_Ico]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hc)
  have he' : ((positions lo hi).card : ℝ) = ((⌈hi-1/2⌉ : ℤ) : ℝ)-⌈lo-1/2⌉ := by exact_mod_cast he
  have h1 := Int.le_ceil (lo-1/2)
  have h2 := Int.ceil_lt_add_one (hi-1/2)
  linarith

def block (s : ℝ) (k : ℤ) : Finset ℤ := positions ((k : ℝ)*s) (((k : ℝ)+1)*s)

def partnerIndex (reverse : Bool) (ν k : ℤ) : ℤ := if reverse then ν-k-1 else k+ν

def overlap (s : ℝ) (reverse : Bool) (a k ν : ℤ) : Finset ℤ :=
  (block s k).filter (fun q => affine reverse a q ∈ block s (partnerIndex reverse ν k))

/-- A central interval survives both translation and reflection. Using one
extra unit of margin removes the open/closed endpoint distinction. -/
theorem core_subset (s : ℝ) (reverse : Bool) (a k ν : ℤ) :
    positions ((k : ℝ)*s+(|a-(ν : ℝ)*s|+1))
      (((k : ℝ)+1)*s-(|a-(ν : ℝ)*s|+1)) ⊆ overlap s reverse a k ν := by
  intro q hq
  obtain ⟨hlo,hhi⟩ := mem_positions.mp hq
  have ha0 := abs_nonneg ((a : ℝ)-(ν : ℝ)*s)
  have ha1 := le_abs_self ((a : ℝ)-(ν : ℝ)*s)
  have ha2 := neg_abs_le ((a : ℝ)-(ν : ℝ)*s)
  refine Finset.mem_filter.mpr ⟨?_,?_⟩
  · apply mem_positions.mpr
    constructor <;> linarith
  · apply mem_positions.mpr
    cases reverse <;> simp only [affine,partnerIndex,Bool.false_eq_true,ite_false,ite_true,
      Int.cast_add,Int.cast_sub,Int.cast_one] <;> constructor <;> nlinarith

/-- An explicit o(s) deficit for the exact grid and signed isometry. -/
theorem overlap_deficit (s : ℝ) (hs : 0 ≤ s) (reverse : Bool) (a k ν : ℤ) :
    (((block s k).card - (overlap s reverse a k ν).card : ℕ) : ℝ) ≤
      2*|a-(ν : ℝ)*s|+4 := by
  have hlo := card_lower ((k : ℝ)*s+(|a-(ν : ℝ)*s|+1))
    (((k : ℝ)+1)*s-(|a-(ν : ℝ)*s|+1))
  have hsub := Finset.card_le_card (core_subset s reverse a k ν)
  have hsub' : ((positions ((k : ℝ)*s+(|a-(ν : ℝ)*s|+1))
    (((k : ℝ)+1)*s-(|a-(ν : ℝ)*s|+1))).card : ℝ) ≤ (overlap s reverse a k ν).card := by exact_mod_cast hsub
  have hhi := card_upper (lo := (k : ℝ)*s) (hi := ((k : ℝ)+1)*s) (by nlinarith)
  have hcard : (overlap s reverse a k ν).card ≤ (block s k).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Nat.cast_sub hcard]
  dsimp [block] at *
  linarith

end

open scoped Classical BigOperators

def inverseOffset (reverse : Bool) (a : ℤ) : ℤ := if reverse then a else -a

theorem affine_inverse (reverse : Bool) (a q : ℤ) :
    affine reverse (inverseOffset reverse a) (affine reverse a q) = q := by
  cases reverse <;> simp [affine,inverseOffset]

theorem affine_injective (reverse : Bool) (a : ℤ) : Function.Injective (affine reverse a) :=
  Function.LeftInverse.injective (affine_inverse reverse a)

theorem partner_inverse (reverse : Bool) (ν k : ℤ) :
    partnerIndex reverse (inverseOffset reverse ν) (partnerIndex reverse ν k) = k := by
  cases reverse <;> simp [partnerIndex,inverseOffset]; omega

/-- The overlap on the partner block is exactly the image of the first overlap. -/
def overlapEquiv (s : ℝ) (reverse : Bool) (a k ν : ℤ) :
    overlap s reverse a k ν ≃
      overlap s reverse (inverseOffset reverse a) (partnerIndex reverse ν k) (inverseOffset reverse ν) where
  toFun q := ⟨affine reverse a q.val, by
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp q.property
    apply Finset.mem_filter.mpr
    exact ⟨hp,by rw [affine_inverse,partner_inverse]; exact hq⟩⟩
  invFun q := ⟨affine reverse (inverseOffset reverse a) q.val,by
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp q.property
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · rwa [partner_inverse] at hp
    · have he : affine reverse a (affine reverse (inverseOffset reverse a) q.val) = q.val := by
        cases reverse <;> simp [affine,inverseOffset]
      rw [he]
      exact hq⟩
  left_inv q := Subtype.ext (affine_inverse reverse a q.val)
  right_inv q := by
    apply Subtype.ext
    cases reverse <;> simp [affine,inverseOffset]

theorem block_disjoint (s : ℝ) (hs : 0 < s) {k j : ℤ} (hne : k ≠ j) :
    Disjoint (block s k) (block s j) := by
  apply Finset.disjoint_left.mpr
  intro q hk hj
  obtain ⟨hk0,hk1⟩ := mem_positions.mp hk
  obtain ⟨hj0,hj1⟩ := mem_positions.mp hj
  rcases lt_or_gt_of_ne hne with hkj | hjk
  · have hh : (k : ℝ)+1 ≤ j := by exact_mod_cast hkj
    nlinarith
  · have hh : (j : ℝ)+1 ≤ k := by exact_mod_cast hjk
    nlinarith

def blockCount (s : ℝ) (ell : ℕ) : ℕ := ⌊(ell : ℝ)/s⌋₊

def tail (s : ℝ) (ell : ℕ) : Finset ℤ := positions ((blockCount s ell : ℝ)*s) ell

theorem count_bound (s : ℝ) (hs : 0 < s) (ell : ℕ) :
    (blockCount s ell : ℝ)*s ≤ ell ∧ (ell : ℝ) < (blockCount s ell+1)*s := by
  have h1 := Nat.floor_le (div_nonneg (Nat.cast_nonneg ell) hs.le)
  have h2 := Nat.lt_floor_add_one ((ell : ℝ)/s)
  constructor
  · exact (le_div_iff₀ hs).mp h1
  · exact (div_lt_iff₀ hs).mp h2

theorem tail_bound (s : ℝ) (hs : 0 < s) (ell : ℕ) :
    ((tail s ell).card : ℝ) ≤ s+1 := by
  have he := count_bound s hs ell
  have hh := card_upper he.1
  dsimp [tail]
  linarith

/-- Literal partition into full blocks and the end fragment. -/
theorem full_or_tail (s : ℝ) (hs : 0 < s) (ell : ℕ) {q : ℤ}
    (hq : q ∈ positions 0 ell) :
    (∃ k : Fin (blockCount s ell), q ∈ block s k.val) ∨ q ∈ tail s ell := by
  obtain ⟨hq0,hq1⟩ := mem_positions.mp hq
  by_cases he : (q : ℝ)+1/2 < (blockCount s ell : ℝ)*s
  · let k := ⌊((q : ℝ)+1/2)/s⌋₊
    have hk : k < blockCount s ell := by
      apply (Nat.floor_lt (div_nonneg hq0 hs.le)).mpr
      exact (div_lt_iff₀ hs).mpr he
    left
    refine ⟨⟨k,hk⟩,?_⟩
    apply mem_positions.mpr
    simp only [Int.cast_natCast]
    exact ⟨(le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hq0 hs.le)),
      (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (((q : ℝ)+1/2)/s))⟩
  · right
    exact mem_positions.mpr ⟨not_lt.mp he,hq1⟩

/-- A full block is entirely within its marked chain. -/
theorem full_subset (s : ℝ) (hs : 0 < s) (ell : ℕ) (k : Fin (blockCount s ell)) :
    block s k.val ⊆ positions 0 ell := by
  intro q hq
  obtain ⟨hlo,hhi⟩ := mem_positions.mp hq
  apply mem_positions.mpr
  have hk : (k.val : ℝ)+1 ≤ blockCount s ell := by exact_mod_cast k.isLt
  have he := (count_bound s hs ell).1
  simp only [Int.cast_natCast] at hlo hhi
  constructor
  · have hkn : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    nlinarith
  · nlinarith

/-- A grid block situated inside a comparison with one-block margins has a
full indicated target block. This includes negative offsets and reflections. -/
theorem partner_full (s : ℝ) (hs : 0 < s) (reverse : Bool) (a k ν : ℤ)
    (lo hi ell : ℝ) (herr : |(a : ℝ)-(ν : ℝ)*s| ≤ s)
    (hlo : lo ≤ (k : ℝ)*s-s) (hhi : ((k : ℝ)+1)*s+s ≤ hi)
    (htarget : if reverse then 0 ≤ (a : ℝ)-hi ∧ (a : ℝ)-lo ≤ ell
      else 0 ≤ lo+(a : ℝ) ∧ hi+(a : ℝ) ≤ ell) :
    0 ≤ partnerIndex reverse ν k ∧ ((partnerIndex reverse ν k : ℤ)+1 : ℝ)*s ≤ ell := by
  have he1 : (a : ℝ)-(ν : ℝ)*s ≤ s := (le_abs_self _).trans herr
  have he2 : -s ≤ (a : ℝ)-(ν : ℝ)*s := by
    have hh := neg_abs_le ((a : ℝ)-(ν : ℝ)*s)
    linarith
  cases reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true,partnerIndex,
    Int.cast_add,Int.cast_sub,Int.cast_one] at htarget ⊢
  · constructor
    · have hz : (0 : ℝ) ≤ (k : ℝ)+(ν : ℝ) := by nlinarith [htarget.1]
      exact_mod_cast hz
    · nlinarith [htarget.2]
  · constructor
    · have hz : (0 : ℝ) ≤ (ν : ℝ)-(k : ℝ)-1 := by nlinarith [htarget.1]
      exact_mod_cast hz
    · nlinarith [htarget.2]

theorem inverse_error (reverse : Bool) (a ν : ℤ) (s : ℝ) :
    |(inverseOffset reverse a : ℝ)-(inverseOffset reverse ν : ℝ)*s| =
      |(a : ℝ)-(ν : ℝ)*s| := by
  cases reverse
  · simp only [inverseOffset,Bool.false_eq_true,ite_false,Int.cast_neg]
    have he : -(a : ℝ)- -(ν : ℝ)*s = -((a : ℝ)-(ν : ℝ)*s) := by ring
    rw [he,abs_neg]
  · rfl

/-- Uniformly bounded exceptional grid indices near one real cut. -/
def nearCut (s t : ℝ) : Finset ℤ := Finset.Icc ⌈t/s-5⌉ ⌊t/s+5⌋

theorem mem_nearCut (s t : ℝ) (k : ℤ) :
    k ∈ nearCut s t ↔ |(k : ℝ)-t/s| ≤ 5 := by
  simp only [nearCut,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem nearCut_card (s t : ℝ) : (nearCut s t).card ≤ 11 := by
  have h1 := Int.le_ceil (t/s-5)
  have h2 := Int.floor_le (t/s+5)
  have hi : ⌊t/s+5⌋+1-⌈t/s-5⌉ ≤ (11 : ℤ) := by
    have hr : ((⌊t/s+5⌋ : ℤ) : ℝ)+1-⌈t/s-5⌉ ≤ 11 := by linarith
    exact_mod_cast hr
  simp only [nearCut,Int.card_Icc]
  omega

/-- A block containing a compared position and avoiding both endpoint
neighborhoods is deep inside that exact comparison interval. -/
theorem margin_of_not_near (s : ℝ) (hs : 0 < s) (lo hi : ℝ) (k q : ℤ)
    (hq : q ∈ block s k) (hdom : q ∈ positions lo hi)
    (hnlo : k ∉ nearCut s lo) (hnhi : k ∉ nearCut s hi) :
    lo ≤ (k : ℝ)*s-s ∧ ((k : ℝ)+1)*s+s ≤ hi := by
  have hlo := not_le.mp (mt (mem_nearCut s lo k).mpr hnlo)
  have hhi := not_le.mp (mt (mem_nearCut s hi k).mpr hnhi)
  obtain ⟨hk0,hk1⟩ := mem_positions.mp hq
  obtain ⟨hq0,hq1⟩ := mem_positions.mp hdom
  rcases (lt_abs.mp hlo) with hl | hl
  · have hz : 5+lo/s < (k : ℝ) := by linarith
    have hz' := (div_lt_iff₀ hs).mp (show lo/s < (k : ℝ)-5 by linarith)
    constructor
    · nlinarith
    · rcases (lt_abs.mp hhi) with hh | hh
      · have ht := (div_lt_iff₀ hs).mp (show hi/s < (k : ℝ)-5 by linarith)
        nlinarith
      · have ht := (lt_div_iff₀ hs).mp (show (k : ℝ)+5 < hi/s by linarith)
        nlinarith
  · have ht := (lt_div_iff₀ hs).mp (show (k : ℝ)+5 < lo/s by linarith)
    nlinarith

end TorsionFreeZeroDivisors.BlockAlignment

/-! Extraction of the actual partial matching of block occurrences from the
original comparison pairing. Comparison sides are retained,
so a block cannot join itself by aggregating several short comparisons. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.EntropyStages
end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors.OccurrenceMatching
open scoped Classical
open EntropyStages
variable {Ω B E : Type*}

structure Data where
  /-- Uniform bound for discarded letters in every selected comparison. -/
  error : ℕ
  positions : B → Finset Ω
  disjoint : ∀ {o p}, o ≠ p → Disjoint (positions o) (positions p)
  pairing : Pairing Ω
  side : Ω → Option E
  flip : E → E
  flip_inv : Function.Involutive flip
  flip_ne : ∀ e, flip e ≠ e
  side_partner : ∀ x e, side x = some e → side (pairing.partner x) = some (flip e)

namespace Data
variable (D : Data (Ω := Ω) (B := B) (E := E))

/-- The positions of one comparison side in a pair of occurrence blocks. -/
def slice (e : E) (o p : B) : Finset Ω :=
  (D.positions o).filter (fun x => D.side x = some e ∧ D.pairing.partner x ∈ D.positions p)

theorem slice_mem {e : E} {o p : B} {x : Ω} :
    x ∈ D.slice e o p ↔ x ∈ D.positions o ∧ D.side x = some e ∧ D.pairing.partner x ∈ D.positions p := by
  simp only [slice,Finset.mem_filter]

def reverseSlice (e : E) (o p : B) : D.slice e o p ≃ D.slice (D.flip e) p o where
  toFun x := ⟨D.pairing.partner x.val,by
    obtain ⟨hx,he,hp⟩ := D.slice_mem.mp x.property
    exact D.slice_mem.mpr ⟨hp,D.side_partner x.val e he,by rwa [D.pairing.involutive]⟩⟩
  invFun x := ⟨D.pairing.partner x.val,by
    obtain ⟨hx,he,hp⟩ := D.slice_mem.mp x.property
    exact D.slice_mem.mpr ⟨hp,by simpa only [D.flip_inv e] using D.side_partner x.val (D.flip e) he,
      by rwa [D.pairing.involutive]⟩⟩
  left_inv x := Subtype.ext (D.pairing.involutive x.val)
  right_inv x := Subtype.ext (D.pairing.involutive x.val)

theorem slice_card (e : E) (o p : B) : (D.slice e o p).card = (D.slice (D.flip e) p o).card := by
  simpa using Fintype.card_congr (D.reverseSlice e o p)

def Joined (o p : B) : Prop :=
  ∃ e, (D.positions o).card < 2*(D.slice e o p).card ∧
    (D.positions p).card < 2*(D.slice e o p).card ∧
    (D.positions o).card ≤ (D.slice e o p).card+D.error ∧
    (D.positions p).card ≤ (D.slice e o p).card+D.error

theorem joined_symm {o p : B} (h : D.Joined o p) : D.Joined p o := by
  obtain ⟨e,ho,hp,heo,hep⟩ := h
  rw [D.slice_card e o p] at ho hp heo hep
  exact ⟨D.flip e,hp,ho,hep,heo⟩

theorem joined_ne {o p : B} (h : D.Joined o p) : o ≠ p := by
  intro he
  subst p
  obtain ⟨e,ho,_⟩ := h
  have hd : Disjoint (D.slice e o o) (D.slice (D.flip e) o o) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (D.slice_mem.mp hx).2.1
    have hy' := (D.slice_mem.mp hy).2.1
    exact D.flip_ne e (Option.some.inj (hy'.symm.trans hx'))
  have hu : D.slice e o o ∪ D.slice (D.flip e) o o ⊆ D.positions o :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hd,← D.slice_card e o o] at hc
  omega

theorem joined_unique {o p q : B} (hp : D.Joined o p) (hq : D.Joined o q) : p = q := by
  by_contra hne
  obtain ⟨e,ho,_⟩ := hp
  obtain ⟨f,ho',_⟩ := hq
  have hd : Disjoint (D.slice e o p) (D.slice f o q) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (D.disjoint hne) (D.slice_mem.mp hx).2.2 (D.slice_mem.mp hy).2.2
  have hu : D.slice e o p ∪ D.slice f o q ⊆ D.positions o :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

def partner (o : B) : B := if h : ∃ p, D.Joined o p then h.choose else o

theorem partner_spec {o p : B} (h : D.Joined o p) : D.partner o = p := by
  unfold partner
  rw [dif_pos ⟨p,h⟩]
  exact D.joined_unique (Exists.choose_spec _) h

theorem partner_involutive : Function.Involutive D.partner := by
  intro o
  by_cases h : ∃ p, D.Joined o p
  · obtain ⟨p,hp⟩ := h
    rw [D.partner_spec hp,D.partner_spec (D.joined_symm hp)]
  · simp only [partner,dif_neg h]

def matching : Pairing B := ⟨D.partner,D.partner_involutive⟩

theorem matched_iff (o : B) : (D.matching.partner o ≠ o) ↔ ∃ p, D.Joined o p := by
  change D.partner o ≠ o ↔ _
  constructor
  · intro h
    by_contra hn
    exact h (by simp [partner,hn])
  · rintro ⟨p,hp⟩
    rw [D.partner_spec hp]
    exact (D.joined_ne hp).symm

theorem unmatched_iff (o : B) : D.matching.partner o = o ↔ ∀ p, ¬D.Joined o p := by
  simpa using not_congr (D.matched_iff o)

/-- Explicit error criterion usable with the half-integer alignment lemma. -/
theorem joined_of_small_deficit {o p : B} {e : E}
    (hbig_o : 2*D.error < (D.positions o).card) (hbig_p : 2*D.error < (D.positions p).card)
    (hdef_o : (D.positions o).card-(D.slice e o p).card ≤ D.error)
    (hdef_p : (D.positions p).card-(D.slice e o p).card ≤ D.error) : D.Joined o p := by
  exact ⟨e,by omega,by omega,by omega,by omega⟩

open scoped BigOperators
variable [Fintype Ω] [Fintype B]

def unmatchedBlocks : Finset B := Finset.univ.filter (fun o => D.matching.partner o = o)
def unpairedPositions : Finset Ω := Finset.univ.filter (fun x => D.pairing.partner x = x)

/-- The source unmatched-block charge, with every rounding/cut error explicit.
Only the stated local geometric coverage of nonexceptional blocks is needed. -/
theorem unmatched_mass (s : ℝ) (hs : 0 ≤ s) (exceptional : Finset B)
    (hsize : ∀ o, s-1 ≤ ((D.positions o).card : ℝ))
    (hcover : ∀ o, D.matching.partner o = o → o ∉ exceptional →
      D.positions o ⊆ D.unpairedPositions) :
    s*(D.unmatchedBlocks.card : ℝ) ≤ (D.unpairedPositions.card : ℝ) +
      s*exceptional.card + Fintype.card B := by
  let good := D.unmatchedBlocks \ exceptional
  have hsubset : good.biUnion D.positions ⊆ D.unpairedPositions := by
    intro x hx
    obtain ⟨o,ho,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨ho,hn⟩ := Finset.mem_sdiff.mp ho
    exact hcover o (Finset.mem_filter.mp ho).2 hn hx
  have hsum : (∑ o ∈ good, (D.positions o).card) ≤ D.unpairedPositions.card := by
    rw [← Finset.card_biUnion (fun o _ p _ hne => D.disjoint hne)]
    exact Finset.card_le_card hsubset
  have hsumr : (∑ o ∈ good, ((D.positions o).card : ℝ)) ≤ D.unpairedPositions.card := by
    exact_mod_cast hsum
  have hlower : s*(good.card : ℝ) ≤ D.unpairedPositions.card + good.card := by
    have hh := Finset.sum_le_sum (s := good) (fun o _ => hsize o)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    nlinarith
  have hcount : D.unmatchedBlocks.card ≤ good.card+exceptional.card := by
    have hh := Finset.card_sdiff_add_card_inter D.unmatchedBlocks exceptional
    have hi := Finset.card_le_card (Finset.inter_subset_right : D.unmatchedBlocks ∩ exceptional ⊆ exceptional)
    dsimp [good]
    omega
  have hcount' : (D.unmatchedBlocks.card : ℝ) ≤ good.card+exceptional.card := by exact_mod_cast hcount
  have hb : (good.card : ℝ) ≤ Fintype.card B := by exact_mod_cast Finset.card_le_univ good
  have hh := mul_le_mul_of_nonneg_left hcount' hs
  nlinarith

end Data
end TorsionFreeZeroDivisors.OccurrenceMatching

/-! The actual common-grid block matching of an affine comparison system.
Positions are the literal half-integer edge indices within each traversal. -/
namespace TorsionFreeZeroDivisors.ComparedBlocks
open scoped Classical BigOperators
open BlockAlignment EntropyStages
variable {T E : Type*}

abbrev Block (s : ℝ) (len : T → ℕ) := (t : T) × Fin (blockCount s (len t))

variable (s : ℝ) (hs : 0 < s) (len : T → ℕ)

def includeBlock (b : Block s len) : block s b.2.val ↪ Position len where
  toFun q := ⟨b.1,⟨q.val,full_subset s hs (len b.1) b.2 q.property⟩⟩
  inj' := by
    intro q r h
    exact Subtype.ext (congrArg (fun x : Position len => x.2.val) h)

def blockPositions (b : Block s len) : Finset (Position len) :=
  (block s b.2.val).attach.map (includeBlock s hs len b)

theorem mem_blockPositions {b : Block s len} {x : Position len} :
    x ∈ blockPositions s hs len b ↔ x.1 = b.1 ∧ x.2.val ∈ block s b.2.val := by
  constructor
  · intro hx
    obtain ⟨y,_,he⟩ := Finset.mem_map.mp hx
    cases he
    exact ⟨rfl,y.property⟩
  · rintro ⟨he,hq⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨x.2.val,hq⟩,Finset.mem_attach _ _,?_⟩
    cases b; cases x; dsimp at he; subst he; rfl

theorem blockPositions_card (b : Block s len) :
    (blockPositions s hs len b).card = (block s b.2.val).card := by
  simp only [blockPositions,Finset.card_map,Finset.card_attach]

theorem blockPositions_disjoint {b c : Block s len} (hne : b ≠ c) :
    Disjoint (blockPositions s hs len b) (blockPositions s hs len c) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨he,hx⟩ := (mem_blockPositions s hs len).mp hx
  obtain ⟨he',hy⟩ := (mem_blockPositions s hs len).mp hy
  have hb : b.1 = c.1 := he.symm.trans he'
  have hk : (b.2.val : ℤ) = c.2.val := by
    by_contra h
    exact Finset.disjoint_left.mp (block_disjoint s hs h) hx hy
  cases b; cases c; dsimp at hb hk; subst hb
  exact hne (by congr 1; apply Fin.ext; exact_mod_cast hk)

include hs in
/-- Exact full-grid-index converse, rather than clipping a target partner. -/
theorem fullIndex {t : T} {k : ℤ} (hk : 0 ≤ k)
    (hfull : ((k : ℝ)+1)*s ≤ len t) :
    ∃ j : Fin (blockCount s (len t)), (j.val : ℤ) = k := by
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  have hle : k.toNat+1 ≤ blockCount s (len t) := by
    apply Nat.le_floor
    rw [Nat.cast_add,Nat.cast_one,hcast]
    exact (le_div_iff₀ hs).mpr hfull
  exact ⟨⟨k.toNat,by omega⟩,Int.toNat_of_nonneg hk⟩

namespace Comparisons
variable (C : Comparisons (E := E) len) (err : ℕ)

def matchingData : OccurrenceMatching.Data (Ω := Position len) (B := Block s len) (E := E) where
  error := err
  positions := blockPositions s hs len
  disjoint := blockPositions_disjoint s hs len
  pairing := C.pairing
  side := C.side
  flip := C.flip
  flip_inv := C.flip_inv
  flip_ne := C.flip_ne
  side_partner := C.side_partner

/-- The literal integer slice before making any near-full grid approximation. -/
def integerSlice (e : E) (b p : Block s len) : Finset ℤ :=
  (block s b.2.val ∩ positions (C.lo e) (C.hi e)).filter
    (fun q => affine (C.reverse e) (C.offset e) q ∈ block s p.2.val)

theorem slice_sources {e : E} {b p : Block s len}
    (hne : ((C.matchingData s hs len err).slice e b p).Nonempty) :
    b.1 = C.source e ∧ p.1 = C.source (C.flip e) := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hb,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
  have hb' := ((mem_blockPositions s hs len).mp hb).1
  have hp' := ((mem_blockPositions s hs len).mp hp).1
  exact ⟨hb'.symm.trans ((C.side_iff x e).mp he).1,
    hp'.symm.trans (C.partner_source x e he)⟩

theorem slice_integer_card {e : E} {b p : Block s len}
    (hsource : b.1 = C.source e) (htarget : p.1 = C.source (C.flip e)) :
    ((C.matchingData s hs len err).slice e b p).card =
      (C.integerSlice s len e b p).card := by
  apply Finset.card_bij (fun x _ => x.2.val)
  · intro x hx
    obtain ⟨hb,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr
      ⟨((mem_blockPositions s hs len).mp hb).2,((C.side_iff x e).mp he).2⟩,?_⟩
    have hh := ((mem_blockPositions s hs len).mp hp).2
    change (C.pairing.partner x).2.val ∈ block s p.2.val at hh
    rwa [C.partner_coordinate x e he] at hh
  · intro x hx y hy he
    have hx' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hx).1).1
    have hy' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hy).1).1
    have hxy := hx'.trans hy'.symm
    cases x; cases y; dsimp at hxy he; subst hxy
    congr 1
    exact Subtype.ext he
  · intro q hq
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hb,he⟩ := Finset.mem_inter.mp hq
    let x : Position len := ⟨b.1,⟨q,full_subset s hs (len b.1) b.2 hb⟩⟩
    have hx : C.side x = some e := (C.side_iff x e).mpr ⟨hsource,he⟩
    refine ⟨x,(OccurrenceMatching.Data.slice_mem _).mpr ⟨?_,hx,?_⟩,rfl⟩
    · exact (mem_blockPositions s hs len).mpr ⟨rfl,hb⟩
    · apply (mem_blockPositions s hs len).mpr
      refine ⟨(C.partner_source x e hx).trans htarget.symm,?_⟩
      change (C.pairing.partner x).2.val ∈ block s p.2.val
      rwa [C.partner_coordinate x e hx]

/-- The original side comparison covers this entire source block. -/
theorem side_of_margin {b : Block s len} {e : E} (hsource : b.1 = C.source e)
    (hlo : C.lo e ≤ (b.2.val : ℝ)*s-s)
    (hhi : ((b.2.val : ℝ)+1)*s+s ≤ C.hi e)
    {x : Position len} (hx : x ∈ blockPositions s hs len b) : C.side x = some e := by
  obtain ⟨he,hx⟩ := (mem_blockPositions s hs len).mp hx
  obtain ⟨hx0,hx1⟩ := mem_positions.mp hx
  apply (C.side_iff x e).mpr
  refine ⟨he.trans hsource,mem_positions.mpr ?_⟩
  simp only [Int.cast_natCast] at hx0 hx1
  constructor <;> linarith

/-- The full slice is exactly the algebraic source overlap. -/
theorem slice_card_eq {b p : Block s len} {e : E} {ν : ℤ}
    (hsource : b.1 = C.source e) (htarget : p.1 = C.source (C.flip e))
    (hindex : (p.2.val : ℤ) = partnerIndex (C.reverse e) ν b.2.val)
    (hlo : C.lo e ≤ (b.2.val : ℝ)*s-s)
    (hhi : ((b.2.val : ℝ)+1)*s+s ≤ C.hi e) :
    ((C.matchingData s hs len err).slice e b p).card =
      (overlap s (C.reverse e) (C.offset e) b.2.val ν).card := by
  apply Finset.card_bij (fun x _ => x.2.val)
  · intro x hx
    obtain ⟨hx,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
    have hc := C.partner_coordinate x e he
    have hm := ((mem_blockPositions s hs len).mp hp).2
    change (C.pairing.partner x).2.val ∈ block s p.2.val at hm
    refine Finset.mem_filter.mpr ⟨((mem_blockPositions s hs len).mp hx).2,?_⟩
    rwa [hc,hindex] at hm
  · intro x hx y hy he
    have hx' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hx).1).1
    have hy' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hy).1).1
    have hxy := hx'.trans hy'.symm
    cases x; cases y; dsimp at hxy he; subst hxy
    congr 1
    exact Subtype.ext he
  · intro q hq
    obtain ⟨hq,hq'⟩ := Finset.mem_filter.mp hq
    let x : Position len := ⟨b.1,⟨q,full_subset s hs (len b.1) b.2 hq⟩⟩
    have hx : x ∈ blockPositions s hs len b := (mem_blockPositions s hs len).mpr ⟨rfl,hq⟩
    have he := C.side_of_margin s hs len hsource hlo hhi hx
    refine ⟨x,(OccurrenceMatching.Data.slice_mem _).mpr ⟨hx,he,?_⟩,rfl⟩
    apply (mem_blockPositions s hs len).mpr
    refine ⟨(C.partner_source x e he).trans htarget.symm,?_⟩
    change (C.pairing.partner x).2.val ∈ block s p.2.val
    rw [C.partner_coordinate x e he,hindex]
    exact hq'

/-- A block deep inside an actual comparison has a near-full selected partner. -/
theorem joined_of_margin {b : Block s len} {e : E} {ν : ℤ}
    (hsource : b.1 = C.source e)
    (hsmall : 2*(err : ℝ) < s-1)
    (herr : 2*|(C.offset e : ℝ)-(ν : ℝ)*s|+4 ≤ err)
    (hlo : C.lo e ≤ (b.2.val : ℝ)*s-s)
    (hhi : ((b.2.val : ℝ)+1)*s+s ≤ C.hi e) :
    ∃ p, (C.matchingData s hs len err).Joined b p := by
  have ha : |(C.offset e : ℝ)-(ν : ℝ)*s| ≤ s := by
    have hh := abs_nonneg ((C.offset e : ℝ)-(ν : ℝ)*s)
    linarith
  obtain ⟨hk0,hk1⟩ := partner_full s hs (C.reverse e) (C.offset e) b.2.val ν
    (C.lo e) (C.hi e) (len (C.source (C.flip e))) ha hlo hhi (C.target_range e)
  obtain ⟨j,hj⟩ := fullIndex s hs len hk0 hk1
  let p : Block s len := ⟨C.source (C.flip e),j⟩
  have hslice := C.slice_card_eq s hs len err hsource (p := p) rfl hj hlo hhi
  refine ⟨p,OccurrenceMatching.Data.joined_of_small_deficit _ (e := e) ?_ ?_ ?_ ?_⟩
  · change 2*err < (blockPositions s hs len b).card
    rw [blockPositions_card]
    have hh := card_lower ((b.2.val : ℝ)*s) (((b.2.val : ℝ)+1)*s)
    have hr : 2*(err : ℝ) < (block s b.2.val).card := by simp only [block,Int.cast_natCast]; nlinarith
    exact_mod_cast hr
  · change 2*err < (blockPositions s hs len p).card
    rw [blockPositions_card]
    have hh := card_lower ((p.2.val : ℝ)*s) (((p.2.val : ℝ)+1)*s)
    have hr : 2*(err : ℝ) < (block s p.2.val).card := by simp only [block,Int.cast_natCast]; nlinarith
    exact_mod_cast hr
  · change (blockPositions s hs len b).card- _ ≤ err
    rw [blockPositions_card,hslice]
    have hh := (overlap_deficit s hs.le (C.reverse e) (C.offset e) b.2.val ν).trans herr
    exact_mod_cast hh
  · change (blockPositions s hs len p).card- _ ≤ err
    rw [blockPositions_card,hslice]
    have hc := Fintype.card_congr (overlapEquiv s (C.reverse e) (C.offset e) b.2.val ν)
    simp only [Fintype.card_coe] at hc
    rw [hc]
    have hh := overlap_deficit s hs.le (C.reverse e) (inverseOffset (C.reverse e) (C.offset e))
      (partnerIndex (C.reverse e) ν b.2.val) (inverseOffset (C.reverse e) ν)
    rw [inverse_error] at hh
    have hr := hh.trans herr
    change ((block s j.val).card - _) ≤ _
    rw [hj]
    exact_mod_cast hr

variable [Fintype T] [Fintype E]

def nearCutBlocks (t : T) (cut : ℝ) : Finset (Block s len) :=
  Finset.univ.filter (fun b => b.1 = t ∧ (b.2.val : ℤ) ∈ nearCut s cut)

theorem nearCutBlocks_card (t : T) (cut : ℝ) : (nearCutBlocks s len t cut).card ≤ 11 := by
  apply le_trans ?_ (nearCut_card s cut)
  refine Finset.card_le_card_of_injOn (fun b : Block s len => (b.2.val : ℤ)) ?_ ?_
  · intro b hb
    exact (Finset.mem_filter.mp hb).2.2
  · intro b hb c hc he
    have hb' := (Finset.mem_filter.mp hb).2.1
    have hc' := (Finset.mem_filter.mp hc).2.1
    have hbc := hb'.trans hc'.symm
    cases b; cases c; dsimp at hbc he; subst hbc
    congr 1
    apply Fin.ext
    exact_mod_cast he

def exceptional : Finset (Block s len) :=
  Finset.univ.biUnion (fun e : E =>
    nearCutBlocks s len (C.source e) (C.lo e) ∪ nearCutBlocks s len (C.source e) (C.hi e))

theorem exceptional_card : (C.exceptional s len).card ≤ 22*Fintype.card E := by
  have h1 := Finset.card_biUnion_le (s := (Finset.univ : Finset E))
    (t := fun e => nearCutBlocks s len (C.source e) (C.lo e) ∪ nearCutBlocks s len (C.source e) (C.hi e))
  have h2 : ∀ e : E, (nearCutBlocks s len (C.source e) (C.lo e) ∪
      nearCutBlocks s len (C.source e) (C.hi e)).card ≤ 22 := by
    intro e
    have h := Finset.card_union_le (nearCutBlocks s len (C.source e) (C.lo e))
      (nearCutBlocks s len (C.source e) (C.hi e))
    have h3 := nearCutBlocks_card s len (C.source e) (C.lo e)
    have h4 := nearCutBlocks_card s len (C.source e) (C.hi e)
    omega
  have h3 := Finset.sum_le_sum (s := (Finset.univ : Finset E)) (fun e _ => h2 e)
  simpa [exceptional,Nat.mul_comm] using h1.trans h3

/-- No point of a deep unmatched block belongs to any original comparison. -/
theorem unmatched_unpaired (ν : E → ℤ)
    (hsmall : 2*(err : ℝ) < s-1)
    (herr : ∀ e, 2*|(C.offset e : ℝ)-(ν e : ℝ)*s|+4 ≤ err)
    {b : Block s len} (hb : (C.matchingData s hs len err).matching.partner b = b)
    (hn : b ∉ C.exceptional s len) :
    blockPositions s hs len b ⊆ (C.matchingData s hs len err).unpairedPositions := by
  intro x hx
  simp only [OccurrenceMatching.Data.unpairedPositions,Finset.mem_filter,Finset.mem_univ,true_and]
  change C.pairing.partner x = x
  apply (C.none_iff x).mp
  cases he : C.side x with
  | none => rfl
  | some e =>
    exfalso
    obtain ⟨hxsource,hdom⟩ := (C.side_iff x e).mp he
    obtain ⟨hxb,hxk⟩ := (mem_blockPositions s hs len).mp hx
    have hsource := hxb.symm.trans hxsource
    have hnlo : (b.2.val : ℤ) ∉ nearCut s (C.lo e) := by
      intro h
      apply hn
      exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsource,h⟩)⟩
    have hnhi : (b.2.val : ℤ) ∉ nearCut s (C.hi e) := by
      intro h
      apply hn
      exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsource,h⟩)⟩
    obtain ⟨hl,hr⟩ := margin_of_not_near s hs (C.lo e) (C.hi e) b.2.val x.2.val hxk hdom hnlo hnhi
    obtain ⟨p,hp⟩ := C.joined_of_margin s hs len err hsource hsmall (herr e) hl hr
    exact (OccurrenceMatching.Data.unmatched_iff _ b).mp hb p hp

include hs in
/-- The full block mass and hence the rounding charge use the total actual
traversal length, with no prescribed occurrence-count estimate. -/
theorem block_mass : s*(Fintype.card (Block s len) : ℝ) ≤ ∑ t, (len t : ℝ) := by
  have he : (Fintype.card (Block s len) : ℝ) = ∑ t, (blockCount s (len t) : ℝ) := by
    simp only [Block,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  simpa [mul_comm] using (count_bound s hs (len t)).1

theorem unmatched_bound (ν : E → ℤ)
    (hsmall : 2*(err : ℝ) < s-1)
    (herr : ∀ e, 2*|(C.offset e : ℝ)-(ν e : ℝ)*s|+4 ≤ err) :
    s*((C.matchingData s hs len err).unmatchedBlocks.card : ℝ) ≤
      (C.matchingData s hs len err).unpairedPositions.card +
      22*s*Fintype.card E + (∑ t, (len t : ℝ))/s := by
  have hm := OccurrenceMatching.Data.unmatched_mass (C.matchingData s hs len err)
    s hs.le (C.exceptional s len) (fun b => ?_) (fun b hb hn =>
      C.unmatched_unpaired s hs len err ν hsmall herr hb hn)
  · have hex : ((C.exceptional s len).card : ℝ) ≤ 22*Fintype.card E := by
      exact_mod_cast C.exceptional_card s len
    have hb : (Fintype.card (Block s len) : ℝ) ≤ (∑ t, (len t : ℝ))/s :=
      (le_div_iff₀ hs).mpr (by simpa [mul_comm] using block_mass s hs len)
    have hmul := mul_le_mul_of_nonneg_left hex hs.le
    nlinarith
  · change s-1 ≤ (blockPositions s hs len b).card
    rw [blockPositions_card]
    have hh := card_lower ((b.2.val : ℝ)*s) (((b.2.val : ℝ)+1)*s)
    simpa [block,mul_add,add_mul] using hh

end Comparisons
end TorsionFreeZeroDivisors.ComparedBlocks

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.AffineIntervals
open scoped Classical
open BlockAlignment

def compOffset (r : Bool) (a b : ℤ) : ℤ := if r then a-b else a+b

lemma affine_comp (r s : Bool) (a b x : ℤ) :
    affine r a (affine s b x)=affine (r.xor s) (compOffset r a b) x := by
  cases r <;> cases s <;> simp [affine,compOffset] <;> ring

/-- Exact integer endpoints of the inverse image; reflection does not incur
any rounding loss on the source half-integer convention. -/
def preLo (r : Bool) (a lo hi : ℤ) : ℤ := if r then a-hi else lo-a
def preHi (r : Bool) (a lo hi : ℤ) : ℤ := if r then a-lo else hi-a

lemma mem_preimage (r : Bool) (a lo hi x : ℤ) :
    affine r a x∈Finset.Ico lo hi ↔ x∈Finset.Ico (preLo r a lo hi) (preHi r a lo hi) := by
  cases r <;> simp only [affine,preLo,preHi,Bool.false_eq_true,ite_false,ite_true,Finset.mem_Ico] <;> omega

lemma preimage_bounds (r : Bool) (a lo hi l h : ℤ)
    (hl : preLo r a lo hi≤l) (hh : h≤preHi r a lo hi) :
    if r then lo≤a-h ∧ a-l≤hi else lo≤l+a ∧ h+a≤hi := by
  cases r <;> simp only [preLo,preHi,Bool.false_eq_true,ite_false,ite_true] at * <;> omega

/-- Empty comparison sides may be placed at the preimage of target boundary
zero; this has no occurrences and satisfies the global range condition. -/
def anchor (r : Bool) (a : ℤ) : ℤ := if r then a else -a

lemma anchor_bounds (r : Bool) (a : ℤ) (n : ℕ) :
    if r then 0≤a-anchor r a ∧ a-anchor r a≤n
    else 0≤anchor r a+a ∧ anchor r a+a≤n := by
  cases r <;> simp [anchor]

end TorsionFreeZeroDivisors.AffineIntervals
namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open BlockAlignment ComparedBlocks AffineIntervals EntropyStages

variable {P T E : Type*} {lp : P → ℕ} {lt : T → ℕ}

/-- A literal partition into signed integer chunks, not a count of formal pieces. -/
structure Chunking (lp : P → ℕ) (lt : T → ℕ) where
  equiv : Position lt ≃ Position lp
  path : T → P
  reverse : T → Bool
  offset : T → ℤ
  source : ∀ x, (equiv x).1 = path x.1
  coordinate : ∀ x, (equiv x).2.val = affine (reverse x.1) (offset x.1) x.2.val

lemma position_ext {x y : Position lp} (hs : x.1=y.1) (hc : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨x,q⟩; rcases y with ⟨y,r⟩
  dsimp at hs hc
  subst y
  congr 1
  exact Subtype.ext hc

namespace Chunking
variable (K : Chunking lp lt) (C : Comparisons (E := E) lp)

def pairing : Pairing (Position lt) where
  partner x := K.equiv.symm (C.pairing.partner (K.equiv x))
  involutive x := by
    dsimp
    rw [K.equiv.apply_symm_apply,C.pairing.involutive (K.equiv x),K.equiv.symm_apply_apply]

lemma partner_image (x : Position lt) :
    K.equiv ((K.pairing C).partner x)=C.pairing.partner (K.equiv x) := by
  simp [pairing]

def rev (e : E) (t u : T) : Bool :=
  (K.reverse u).xor ((C.reverse e).xor (K.reverse t))

def off (e : E) (t u : T) : ℤ :=
  compOffset (K.reverse u) (inverseOffset (K.reverse u) (K.offset u))
    (compOffset (C.reverse e) (C.offset e) (K.offset t))

lemma new_affine (e : E) (t u : T) (q : ℤ) :
    affine (K.rev C e t u) (K.off C e t u) q =
      affine (K.reverse u) (inverseOffset (K.reverse u) (K.offset u))
        (affine (C.reverse e) (C.offset e) (affine (K.reverse t) (K.offset t) q)) := by
  rw [affine_comp (C.reverse e) (K.reverse t),affine_comp]
  rfl

lemma new_affine_image (e : E) (t u : T) (q : ℤ) :
    affine (K.reverse u) (K.offset u) (affine (K.rev C e t u) (K.off C e t u) q) =
      affine (C.reverse e) (C.offset e) (affine (K.reverse t) (K.offset t) q) := by
  rw [K.new_affine]
  generalize affine (C.reverse e) (C.offset e) (affine (K.reverse t) (K.offset t) q) = z
  cases K.reverse u <;> simp [affine,inverseOffset]

lemma partner_coordinate {x : Position lt} {e : E} (he : C.side (K.equiv x)=some e) :
    ((K.pairing C).partner x).2.val =
      affine (K.rev C e x.1 ((K.pairing C).partner x).1)
        (K.off C e x.1 ((K.pairing C).partner x).1) x.2.val := by
  have h := C.partner_coordinate (K.equiv x) e he
  rw [← K.partner_image, K.coordinate, K.coordinate] at h
  apply affine_injective (K.reverse ((K.pairing C).partner x).1)
    (K.offset ((K.pairing C).partner x).1)
  rw [K.new_affine_image]
  exact h

/-- The image of an old partner is in a given chunk precisely when the
conjugate affine index is in that chunk. -/
lemma partner_chunk_iff {x : Position lt} {e : E} {u : T}
    (he : C.side (K.equiv x)=some e) (hu : K.path u=C.source (C.flip e)) :
    ((K.pairing C).partner x).1=u ↔
      affine (K.rev C e x.1 u) (K.off C e x.1 u) x.2.val ∈ positions 0 (lt u) := by
  constructor
  · intro h
    have hm := ((K.pairing C).partner x).2.property
    rw [K.partner_coordinate C he,h] at hm
    exact hm
  · intro hm
    let y : Position lt := ⟨u,⟨_,hm⟩⟩
    have hy : K.equiv y=C.pairing.partner (K.equiv x) := by
      apply position_ext
      · rw [K.source,C.partner_source _ _ he]
        exact hu
      · rw [K.coordinate,C.partner_coordinate _ _ he,K.coordinate]
        exact K.new_affine_image C e x.1 u x.2.val
    have : y=(K.pairing C).partner x := K.equiv.injective (hy.trans (K.partner_image C x).symm)
    exact (congrArg Sigma.fst this).symm

variable (lo hi : E → ℤ)

def rawLo (e : E) (t u : T) : ℤ :=
  max 0 (max (preLo (K.reverse t) (K.offset t) (lo e) (hi e))
    (preLo (K.rev C e t u) (K.off C e t u) 0 (lt u)))
def rawHi (e : E) (t u : T) : ℤ :=
  min (lt t) (min (preHi (K.reverse t) (K.offset t) (lo e) (hi e))
    (preHi (K.rev C e t u) (K.off C e t u) 0 (lt u)))

def valid (e : E) (t u : T) : Prop :=
  K.path t=C.source e ∧ K.path u=C.source (C.flip e) ∧
    K.rawLo C lo hi e t u ≤ K.rawHi C lo hi e t u

def lower (e : E) (t u : T) : ℤ :=
  if K.valid C lo hi e t u then K.rawLo C lo hi e t u
  else anchor (K.rev C e t u) (K.off C e t u)
def upper (e : E) (t u : T) : ℤ :=
  if K.valid C lo hi e t u then K.rawHi C lo hi e t u
  else anchor (K.rev C e t u) (K.off C e t u)

variable (hlo : ∀ e, C.lo e=(lo e : ℝ)) (hhi : ∀ e, C.hi e=(hi e : ℝ))

include hlo hhi in
lemma interval_iff (x : Position lt) (e : E) (u : T) :
    x.2.val ∈ positions (K.lower C lo hi e x.1 u) (K.upper C lo hi e x.1 u) ↔
      C.side (K.equiv x)=some e ∧ ((K.pairing C).partner x).1=u := by
  rw [integer_positions]
  by_cases hv : K.valid C lo hi e x.1 u
  · rw [lower,upper,if_pos hv,if_pos hv]
    have hx := x.2.property
    simp only [nat_positions] at hx
    have hpart := hv.1
    have htarget := hv.2.1
    have hmem : x.2.val ∈ Finset.Ico (K.rawLo C lo hi e x.1 u) (K.rawHi C lo hi e x.1 u) ↔
        affine (K.reverse x.1) (K.offset x.1) x.2.val ∈ Finset.Ico (lo e) (hi e) ∧
        affine (K.rev C e x.1 u) (K.off C e x.1 u) x.2.val ∈ Finset.Ico (0:ℤ) (lt u:ℤ) := by
      rw [mem_preimage,mem_preimage]
      simp only [rawLo,rawHi,Finset.mem_Ico,max_le_iff,lt_min_iff]
      simp only [Finset.mem_Ico] at hx
      omega
    rw [hmem]
    have hside : C.side (K.equiv x)=some e ↔
        affine (K.reverse x.1) (K.offset x.1) x.2.val ∈ Finset.Ico (lo e) (hi e) := by
      rw [C.side_iff,K.coordinate]
      simp only [K.source,hlo,hhi,integer_positions]
      exact and_iff_right hpart
    rw [← hside]
    apply and_congr_right
    intro he
    rw [K.partner_chunk_iff C he htarget]
    simp only [nat_positions]
  · rw [lower,upper,if_neg hv,if_neg hv,Finset.Ico_self]
    simp only [Finset.notMem_empty,false_iff,not_and]
    intro he hu
    apply hv
    have hp := (C.side_iff (K.equiv x) e).mp he
    have ht := C.partner_source (K.equiv x) e he
    rw [← K.partner_image,K.source,hu] at ht
    refine ⟨(K.source x).symm.trans hp.1,ht,?_⟩
    have hq := hp.2
    rw [hlo,hhi,integer_positions,K.coordinate,mem_preimage] at hq
    have hr := (K.partner_chunk_iff C he ht).mp hu
    simp only [nat_positions] at hr
    rw [mem_preimage] at hr
    have hx := x.2.property
    simp only [nat_positions] at hx
    simp only [Finset.mem_Ico] at hx hq hr
    simp only [rawLo,rawHi,max_le_iff,le_min_iff]
    omega

lemma range_bounds (e : E) (t u : T) :
    if K.rev C e t u then
      0≤K.off C e t u-K.upper C lo hi e t u ∧ K.off C e t u-K.lower C lo hi e t u≤lt u
    else 0≤K.lower C lo hi e t u+K.off C e t u ∧ K.upper C lo hi e t u+K.off C e t u≤lt u := by
  by_cases hv : K.valid C lo hi e t u
  · simp only [lower,upper,if_pos hv]
    apply preimage_bounds
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  · simp only [lower,upper,if_neg hv]
    exact anchor_bounds _ _ _

def side (x : Position lt) : Option (E×T×T) :=
  (C.side (K.equiv x)).map (fun e => (e,x.1,((K.pairing C).partner x).1))

lemma side_iff (x : Position lt) (e : E) (t u : T) :
    K.side C x=some (e,t,u) ↔
      C.side (K.equiv x)=some e ∧ x.1=t ∧ ((K.pairing C).partner x).1=u := by
  cases h : C.side (K.equiv x) <;> simp [side,h,Prod.mk.injEq]

/-- Split every side at the boundaries of both chunks. Empty pieces carry no
positions; their chosen endpoint maintains the exact range convention. -/
def comparisons : Comparisons (E := E×T×T) lt where
  pairing := K.pairing C
  side := K.side C
  flip a := (C.flip a.1,a.2.2,a.2.1)
  flip_inv a := by rcases a with ⟨e,t,u⟩; simp [C.flip_inv e]
  flip_ne a := by
    intro h
    exact C.flip_ne a.1 (congrArg Prod.fst h)
  side_partner x a ha := by
    rcases a with ⟨e,t,u⟩
    obtain ⟨he,ht,hu⟩ := (K.side_iff C x e t u).mp ha
    apply (K.side_iff C _ _ _ _).mpr
    refine ⟨?_,hu,?_⟩
    · rw [K.partner_image]
      exact C.side_partner (K.equiv x) e he
    · rw [(K.pairing C).involutive x]
      exact ht
  none_iff x := by
    simp only [side,Option.map_eq_none_iff,C.none_iff]
    constructor
    · intro h
      apply K.equiv.injective
      rw [K.partner_image,h]
    · intro h
      rw [← K.partner_image,h]
  source a := a.2.1
  lo a := K.lower C lo hi a.1 a.2.1 a.2.2
  hi a := K.upper C lo hi a.1 a.2.1 a.2.2
  reverse a := K.rev C a.1 a.2.1 a.2.2
  offset a := K.off C a.1 a.2.1 a.2.2
  side_iff x a := by
    rcases a with ⟨e,t,u⟩
    rw [K.side_iff]
    constructor
    · rintro ⟨he,ht,hu⟩
      refine ⟨ht,?_⟩
      subst t
      exact (K.interval_iff C lo hi hlo hhi x e u).mpr ⟨he,hu⟩
    · rintro ⟨ht,hm⟩
      change x.1=t at ht
      subst t
      obtain ⟨he,hu⟩ := (K.interval_iff C lo hi hlo hhi x e u).mp hm
      exact ⟨he,rfl,hu⟩
  partner_source x a ha := ((K.side_iff C x a.1 a.2.1 a.2.2).mp ha).2.2
  partner_coordinate x a ha := by
    obtain ⟨he,ht,hu⟩ := (K.side_iff C x a.1 a.2.1 a.2.2).mp ha
    simpa only [ht,hu] using K.partner_coordinate C he
  target_range a := by
    have h := K.range_bounds C lo hi a.1 a.2.1 a.2.2
    cases hr : K.rev C a.1 a.2.1 a.2.2 <;> simp only [hr,Bool.false_eq_true,ite_false,ite_true] at h ⊢
    · exact_mod_cast h
    · exact_mod_cast h

lemma fixed_iff (x : Position lt) :
    (K.pairing C).partner x=x ↔ C.pairing.partner (K.equiv x)=K.equiv x := by
  constructor
  · intro h
    rw [← K.partner_image,h]
  · intro h
    apply K.equiv.injective
    rw [K.partner_image,h]

def unpairedEquiv : {x : Position lt // (K.pairing C).partner x=x} ≃
    {x : Position lp // C.pairing.partner x=x} :=
  K.equiv.subtypeEquiv (K.fixed_iff C)

lemma xor_labels {A : Type*} (bar : A → A) (hb : Function.Involutive bar)
    (r s t : Bool) (x y : A)
    (h : (if r then bar x else x) = if s then
      bar (if t then bar y else y) else (if t then bar y else y)) :
    x = if t.xor (s.xor r) then bar y else y := by
  have hbb (z : A) : bar (bar z)=z := hb z
  cases r <;> cases s <;> cases t <;> simp only [Bool.xor_false,Bool.xor_true,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,hbb] at h ⊢
  all_goals first | exact h | simpa only [hbb] using congrArg bar h

/-- Every literal compatible labeling survives splitting with exactly the
xor of the path comparison and the two chain orientations. -/
theorem compatible {A : Type*} (bar : A → A) (hb : Function.Involutive bar)
    (old : Position lp → A) (word : Position lt → A)
    (hn : ∀ x,old (K.equiv x)=if K.reverse x.1 then bar (word x) else word x)
    (hc : ∀ x e,C.side x=some e → old x = if C.reverse e then
      bar (old (C.pairing.partner x)) else old (C.pairing.partner x)) :
    ∀ x a, (K.comparisons C lo hi hlo hhi).side x=some a →
      word x=if (K.comparisons C lo hi hlo hhi).reverse a then
        bar (word ((K.comparisons C lo hi hlo hhi).pairing.partner x))
      else word ((K.comparisons C lo hi hlo hhi).pairing.partner x) := by
  intro x a ha
  obtain ⟨he,ht,hu⟩ := (K.side_iff C x a.1 a.2.1 a.2.2).mp ha
  have h := hc (K.equiv x) a.1 he
  rw [← K.partner_image,hn,hn] at h
  have h' := xor_labels bar hb (K.reverse x.1) (C.reverse a.1)
    (K.reverse ((K.pairing C).partner x).1) (word x) (word ((K.pairing C).partner x)) h
  change word x=(if K.rev C a.1 a.2.1 a.2.2 then
    bar (word ((K.pairing C).partner x)) else word ((K.pairing C).partner x))
  dsimp only [rev]
  exact h'.trans (by congr 1; simp only [ht,hu])

end Chunking
end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.FiniteChunking
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks AffineIntervals ChunkComparisons

variable {n : ℕ}

def before (i : Fin n) : Finset (Fin n) := Finset.univ.filter (fun j => j < i)
def start (f : Fin n → ℕ) (i : Fin n) : ℕ := ∑ j∈before i,f j

lemma not_before (i : Fin n) : i∉before i := by simp [before]

lemma start_next (f : Fin n → ℕ) {i j : Fin n} (h : i < j) :
    start f i+f i ≤ start f j := by
  rw [start,add_comm,← Finset.sum_insert (not_before i)]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl|hk
  · simpa [before] using h
  · have hk' : k < i := by simpa [before] using hk
    simpa [before] using hk'.trans h

lemma start_end (f : Fin n → ℕ) (i : Fin n) : start f i+f i ≤ ∑ j,f j := by
  rw [start,add_comm,← Finset.sum_insert (not_before i)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def localIndex (r : Bool) (n : ℕ) (q : ℤ) : ℤ := affine r (if r then n else 0) q

lemma local_bounds (r : Bool) (n : ℕ) {q : ℤ} (hq : q∈positions 0 n) :
    0≤localIndex r n q ∧ localIndex r n q<n := by
  simp only [nat_positions,Finset.mem_Ico] at hq
  cases r <;> simp only [localIndex,affine,Bool.false_eq_true,ite_false,ite_true] <;> omega

lemma affine_offset (r : Bool) (pre len : ℕ) (q : ℤ) :
    affine r (pre+(if r then (len:ℤ) else 0)) q = pre+localIndex r len q := by
  cases r <;> simp [localIndex,affine] <;> omega

lemma positions_card (n : ℕ) : (positions 0 n).card=n := by
  rw [nat_positions,Int.card_Ico,sub_zero,Int.toNat_natCast]

lemma position_card {T : Type*} [Fintype T] (len : T → ℕ) :
    Fintype.card (Position len)=∑ t,len t := by
  simp only [Position,Fintype.card_sigma,Fintype.card_coe,positions_card]

variable {P : Type*} [Fintype P] (chunks : P → ℕ)
  (len : (p : P) → Fin (chunks p) → ℕ) (rev : (p : P) → Fin (chunks p) → Bool)

abbrev traversalLength : Traversal chunks → ℕ := fun t => len t.1 t.2

def offset (t : Traversal chunks) : ℤ := start (len t.1) t.2 + if rev t.1 t.2 then (len t.1 t.2:ℤ) else 0

def image (x : Position (traversalLength chunks len)) : Position (pathLength chunks len) :=
  ⟨x.1.1,⟨affine (rev x.1.1 x.1.2) (offset chunks len rev x.1) x.2.val,by
    simp only [nat_positions,Finset.mem_Ico]
    have hq := local_bounds (rev x.1.1 x.1.2) (len x.1.1 x.1.2) x.2.property
    have hp : (start (len x.1.1) x.1.2:ℤ)+len x.1.1 x.1.2 ≤ pathLength chunks len x.1.1 := by
      exact_mod_cast start_end (len x.1.1) x.1.2
    rw [offset,affine_offset]
    have hz : (0:ℤ)≤ start (len x.1.1) x.1.2 := Int.natCast_nonneg _
    omega⟩⟩

omit [Fintype P] in
lemma image_val (x : Position (traversalLength chunks len)) :
    (image chunks len rev x).2.val =
      start (len x.1.1) x.1.2+localIndex (rev x.1.1 x.1.2) (len x.1.1 x.1.2) x.2.val :=
  affine_offset _ _ _ _

omit [Fintype P] in
lemma image_injective : Function.Injective (image chunks len rev) := by
  rintro ⟨⟨p,i⟩,q⟩ ⟨⟨r,j⟩,v⟩ hh
  have hp : p=r := congrArg Sigma.fst hh
  subst r
  have hc := congrArg (fun x : Position (pathLength chunks len) => x.2.val) hh
  rw [image_val,image_val] at hc
  dsimp only at hc
  have hq := local_bounds (rev p i) (len p i) q.property
  have hv := local_bounds (rev p j) (len p j) v.property
  have he : i=j := by
    rcases lt_trichotomy i j with hij|hij|hji
    · have hpre : (start (len p) i:ℤ)+len p i ≤ start (len p) j := by
        exact_mod_cast start_next (len p) hij
      omega
    · exact hij
    · have hpre : (start (len p) j:ℤ)+len p j ≤ start (len p) i := by
        exact_mod_cast start_next (len p) hji
      omega
  subst j
  have hqv : q=v := by
    apply Subtype.ext
    apply affine_injective (rev p i) (if rev p i then (len p i:ℤ) else 0)
    unfold localIndex at hc
    omega
  subst v
  rfl

/-- The prescribed offsets define an actual equivalence. In particular, this
partition covers every old letter even when a path is empty. -/
def equiv : Position (traversalLength chunks len) ≃ Position (pathLength chunks len) :=
  Equiv.ofBijective (image chunks len rev) <|
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨image_injective chunks len rev,by
      simp only [position_card,Fintype.sum_sigma,traversalLength,pathLength]⟩

def chunking : Chunking (pathLength chunks len) (traversalLength chunks len) where
  equiv := equiv chunks len rev
  path t := t.1
  reverse t := rev t.1 t.2
  offset := offset chunks len rev
  source _ := rfl
  coordinate _ := rfl

end TorsionFreeZeroDivisors.FiniteChunking

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision

namespace PortGraph
variable {V D : Type*} (Γ : PortGraph V D)

@[simp] theorem adj_original (v w : V) : ¬ Γ.subdivision.Adj (.inl v) (.inl w) := id
@[simp] theorem adj_original_port (v : V) (d : D) :
    Γ.subdivision.Adj (.inl v) (.inr d) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_port_original (v : V) (d : D) :
    Γ.subdivision.Adj (.inr d) (.inl v) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_ports (d e : D) :
    Γ.subdivision.Adj (.inr d) (.inr e) ↔ Γ.reverse d = e := Iff.rfl

theorem port_adj_iff (d : D) (a : V ⊕ D) :
    Γ.subdivision.Adj (.inr d) a ↔ a = .inl (Γ.origin d) ∨ a = .inr (Γ.reverse d) := by
  cases a <;> simp [eq_comm]

/-- Every cycle through a port uses its middle edge, since the other port
neighbor is unique and the cycle cannot immediately backtrack. -/
theorem cycle_middle_at_port (d : D) (p : Γ.subdivision.Walk (.inr d) (.inr d))
    (hp : p.IsCycle) : s(Sum.inr d,Sum.inr (Γ.reverse d)) ∈ p.edges := by
  have ha := (Γ.port_adj_iff d p.snd).mp (p.adj_snd hp.not_nil)
  have hb := (Γ.port_adj_iff d p.penultimate).mp (p.adj_penultimate hp.not_nil).symm
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact False.elim (hp.snd_ne_penultimate (ha.trans hb.symm))
    · have he := p.mk_penultimate_end_mem_edges hp.not_nil
      rw [hb,Sym2.eq_swap] at he
      exact he
  · simpa only [ha] using p.mk_start_snd_mem_edges hp.not_nil

/-- No cycle lives entirely in the spokes; a short cycle always gives a
middle edge eligible for a matching transposition. -/
theorem cycle_has_middle [DecidableEq V] [DecidableEq D] {a : V ⊕ D}
    (p : Γ.subdivision.Walk a a) (hp : p.IsCycle) :
    ∃ d, s(Sum.inr d,Sum.inr (Γ.reverse d)) ∈ p.edges := by
  have hex : ∃ d, Sum.inr d ∈ p.support := by
    cases a with
    | inr d => exact ⟨d,p.start_mem_support⟩
    | inl v =>
      have ha := p.adj_snd hp.not_nil
      cases hs : p.snd with
      | inl w => rw [hs] at ha; exact False.elim ha
      | inr d => exact ⟨d,hs ▸ p.snd_mem_support_of_mem_edges (p.mk_start_snd_mem_edges hp.not_nil)⟩
  obtain ⟨d,hd⟩ := hex
  refine ⟨d,?_⟩
  have he := Γ.cycle_middle_at_port d (p.rotate (.inr d) hd) (hp.rotate hd)
  exact (p.rotate_edges (.inr d) hd).mem_iff.mp he

/-- The neighbor fiber at an original vertex is exactly its port fiber. -/
def originalNeighborEquiv (v : V) :
    Γ.subdivision.neighborSet (.inl v) ≃ {d : D // Γ.origin d = v} where
  toFun n := match n with
    | ⟨.inl _,h⟩ => False.elim h
    | ⟨.inr d,h⟩ => ⟨d,h⟩
  invFun d := ⟨.inr d.val,d.property⟩
  left_inv n := by rcases n with ⟨v|d,h⟩; exact False.elim h; rfl
  right_inv _ := rfl

/-- A port has exactly two neighbors: its original vertex and its reverse port.
They lie in disjoint summands even when the original edge is a graph loop. -/
def portNeighborEquiv (d : D) : Γ.subdivision.neighborSet (.inr d) ≃ Bool where
  toFun n := match n.val with | .inl _ => false | .inr _ => true
  invFun b := if b then ⟨.inr (Γ.reverse d),rfl⟩ else ⟨.inl (Γ.origin d),rfl⟩
  left_inv n := by
    rcases n with ⟨v|e,h⟩
    · apply Subtype.ext
      exact congrArg Sum.inl h
    · apply Subtype.ext
      exact congrArg Sum.inr h
  right_inv b := by cases b <;> rfl

theorem card_original_neighbors (v : V) :
    Nat.card (Γ.subdivision.neighborSet (.inl v)) =
      Nat.card {d : D // Γ.origin d = v} := Nat.card_congr (Γ.originalNeighborEquiv v)

theorem card_port_neighbors (d : D) : Nat.card (Γ.subdivision.neighborSet (.inr d)) = 2 := by
  rw [Nat.card_congr (Γ.portNeighborEquiv d)]
  simp

/-- Conjugating the reversal while keeping port origins fixed is a
matching switch, not a relabeling of the original graph. -/
def moveMatches (σ : Equiv.Perm D) : PortGraph V D where
  origin := Γ.origin
  reverse d := σ (Γ.reverse (σ.symm d))
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have h' := congrArg σ.symm h
    simp only [Equiv.symm_apply_apply] at h'
    exact Γ.reverse_ne (σ.symm d) h'

section Switching
variable [DecidableEq D]

/-- Transpose two equally oriented ports. Their reverse ports are not moved. -/
def switch (d e : D) : PortGraph V D := Γ.moveMatches (Equiv.swap d e)

@[simp] theorem switch_origin (d e f : D) : (Γ.switch d e).origin f = Γ.origin f := rfl

/-- The subdivision changes exactly the two middle edges, preserving every
origin-port incidence, including incidences belonging to original loops. -/
theorem switch_adj (d e : D) (hde : d ≠ e) (hdr : d ≠ Γ.reverse e)
    (a b : V ⊕ D) :
    (Γ.switch d e).subdivision.Adj a b ↔
      (Γ.subdivision.Adj a b ∧ s(a,b) ≠ s(Sum.inr d,Sum.inr (Γ.reverse d)) ∧
        s(a,b) ≠ s(Sum.inr e,Sum.inr (Γ.reverse e))) ∨
      s(a,b) = s(Sum.inr d,Sum.inr (Γ.reverse e)) ∨
      s(a,b) = s(Sum.inr e,Sum.inr (Γ.reverse d)) := by
  have hrd : Γ.reverse d ≠ d := Γ.reverse_ne d
  have hre : Γ.reverse e ≠ e := Γ.reverse_ne e
  have hrd_e : Γ.reverse d ≠ e := by
    intro h
    apply hdr
    rw [← h,Γ.reverse_reverse]
  have hrev : Γ.reverse d ≠ Γ.reverse e := fun h => hde (Γ.reverse_reverse.injective h)
  cases a with
  | inl a =>
    cases b <;> simp [subdivision,switch_origin]
  | inr f =>
    cases b with
    | inl b => simp [subdivision,switch_origin]
    | inr g =>
      change (Equiv.swap d e) (Γ.reverse ((Equiv.swap d e) f)) = g ↔ _
      simp only [adj_ports,Sym2.eq_iff,Sum.inr.injEq]
      by_cases hfd : f = d
      · subst f
        simp only [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hdr.symm hre]
        grind
      · by_cases hfe : f = e
        · subst f
          simp only [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hrd hrd_e]
          grind
        · by_cases hfrd : f = Γ.reverse d
          · subst f
            simp only [Equiv.swap_apply_of_ne_of_ne hrd hrd_e,reverse_reverse_apply,
              Equiv.swap_apply_left]
            grind
          · by_cases hfre : f = Γ.reverse e
            · subst f
              simp only [Equiv.swap_apply_of_ne_of_ne hdr.symm hre,reverse_reverse_apply,
                Equiv.swap_apply_right]
              grind
            · have hrfd : Γ.reverse f ≠ d := by
                intro h
                apply hfrd
                rw [← h,Γ.reverse_reverse]
              have hrfe : Γ.reverse f ≠ e := by
                intro h
                apply hfre
                rw [← h,Γ.reverse_reverse]
              simp [Equiv.swap_apply_of_ne_of_ne hfd hfe,
                Equiv.swap_apply_of_ne_of_ne hrfd hrfe,hfd,hfe,hfrd,hfre]

/-- Transposing two occurrences of the same label preserves every port label. -/
theorem label_swap {T : Type*} (label : D → T) (d e : D) (h : label d = label e)
    (f : D) : label ((Equiv.swap d e) f) = label f := by
  by_cases hfd : f = d
  · subst f; simpa using h.symm
  · by_cases hfe : f = e
    · subst f; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hfd hfe]

theorem switch_preserves_labels {T : Type*} (label : D → T) (bar : T → T)
    (hlabel : ∀ f, label (Γ.reverse f) = bar (label f))
    (d e : D) (h : label d = label e) (f : D) :
    label ((Γ.switch d e).reverse f) = bar (label f) := by
  change label ((Equiv.swap d e) (Γ.reverse ((Equiv.swap d e) f))) = bar (label f)
  rw [label_swap label d e h, hlabel, label_swap label d e h]

end Switching

namespace Walk
variable {Γ} {a b c : V}

end Walk
end PortGraph
end TorsionFreeZeroDivisors.PortSubdivision

/-!
Quantitative edge switching for the girth conditioning in types.tex 116–147.
The simple-graph lemmas are also applicable to the canonical threefold
subdivision of a port multigraph (loops become triangles). No random-graph
existence or cone-topology conclusion is assumed in these lemmas.
-/

namespace TorsionFreeZeroDivisors.GirthSwitch

open SimpleGraph
open scoped ENNReal

variable {V : Type*} {G H : SimpleGraph V} {a b x y : V}

/-- Decompose at a specified edge occurrence, with its actual orientation. -/
theorem split_at_edge (p : G.Walk a b) (e : Sym2 V) (he : e ∈ p.edges) :
    ∃ (x y : V) (hxy : G.Adj x y) (p₁ : G.Walk a x) (p₂ : G.Walk y b),
      s(x,y) = e ∧ p = p₁.append (.cons hxy p₂) := by
  induction p with
  | nil => simp at he
  | @cons u v w huv p ih =>
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · exact ⟨u,v,huv,.nil,p,he.symm,rfl⟩
    · obtain ⟨x,y,hxy,p₁,p₂,hxe,hp⟩ := ih he
      exact ⟨x,y,hxy,.cons huv p₁,p₂,hxe,by rw [hp]; rfl⟩

/-- Removing an edge of a closed trail leaves an alternate walk one shorter,
without using the removed edge. -/
theorem alternate_walk (p : G.Walk a a) (hp : p.IsTrail)
    (e : Sym2 V) (he : e ∈ p.edges) :
    ∃ (x y : V) (q : G.Walk x y),
      s(x,y) = e ∧ e ∉ q.edges ∧ q.length + 1 = p.length := by
  obtain ⟨x,y,hxy,p₁,p₂,hxe,hpdecomp⟩ := split_at_edge p e he
  subst p
  have hn := hp.edges_nodup
  simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append,
    List.nodup_cons] at hn
  have hleft : e ∉ p₁.edges := by
    intro ht
    exact hn.2.2 e ht e (by simp [hxe]) rfl
  have hright : e ∉ p₂.edges := by simpa only [hxe] using hn.2.1.1
  refine ⟨y,x,p₂.append p₁,?_,?_,?_⟩
  · simpa only [Sym2.eq_swap] using hxe
  · simp only [Walk.edges_append, List.mem_append, not_or]
    exact ⟨hright,hleft⟩
  · simp only [Walk.length_append, Walk.length_cons]
    omega

/-- Adjoining one new edge. -/
def addEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet {s(x,y)}

@[simp] theorem addEdge_adj (u v : V) :
    (addEdge G x y).Adj u v ↔ G.Adj u v ∨ (s(u,v) = s(x,y) ∧ u ≠ v) := by
  simp [addEdge, SimpleGraph.fromEdgeSet_adj]

/-- A walk avoiding the newly adjoined edge lies in the old graph. -/
theorem transfer_addEdge (p : (addEdge G x y).Walk a b)
    (hp : s(x,y) ∉ p.edges) :
    ∃ q : G.Walk a b, q.length = p.length := by
  refine ⟨p.transfer G ?_,Walk.length_transfer ..⟩
  intro e he
  have hg := p.edges_subset_edgeSet he
  simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
  rcases hg with hg | ⟨rfl,_⟩
  · exact hg
  · exact False.elim (hp he)

/-- Adding an edge whose endpoints have no short old connecting path preserves
the lower girth bound. The path hypothesis includes either orientation. -/
theorem girth_addEdge (L : ℕ) (hG : (L : ℕ∞) ≤ G.egirth)
    (hx : ∀ p : G.Walk x y, L ≤ p.length + 1) :
    (L : ℕ∞) ≤ (addEdge G x y).egirth := by
  classical
  rw [SimpleGraph.le_egirth]
  intro a p hp
  by_cases he : s(x,y) ∈ p.edges
  · obtain ⟨u,v,q,huv,hqe,hql⟩ := alternate_walk p hp.isTrail _ he
    obtain ⟨q',hq'⟩ := transfer_addEdge q hqe
    have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa only [Sym2.eq_iff] using huv
    have hl : L ≤ q'.length + 1 := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx q'
      · simpa only [Walk.length_reverse] using hx q'.reverse
    rw [hq',hql] at hl
    exact_mod_cast hl
  · have htransfer : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
      intro e he'
      have hg := p.edges_subset_edgeSet he'
      simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
      rcases hg with hg | ⟨rfl,_⟩
      · exact hg
      · exact False.elim (he he')
    have hh := SimpleGraph.le_egirth.mp hG a (p.transfer G htransfer) (hp.transfer htransfer)
    simpa only [Walk.length_transfer] using hh

/-- Before the first occurrence of a new edge, a walk lies wholly in G.
No simplicity assumption is required for this decomposition. -/
theorem first_new_edge (p : (addEdge G x y).Walk a b) :
    (∃ q : G.Walk a b, q.length ≤ p.length) ∨
    (∃ q : G.Walk a x, q.length + 1 ≤ p.length) ∨
    (∃ q : G.Walk a y, q.length + 1 ≤ p.length) := by
  induction p with
  | nil => exact Or.inl ⟨.nil,le_rfl⟩
  | @cons u v w huv p ih =>
    rcases (addEdge_adj u v).mp huv with hold | ⟨he,_⟩
    · rcases ih with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
      · exact Or.inl ⟨.cons hold q, by simpa only [Walk.length_cons] using Nat.add_le_add_right hq 1⟩
      · exact Or.inr (Or.inl ⟨.cons hold q, by simp only [Walk.length_cons]; omega⟩)
      · exact Or.inr (Or.inr ⟨.cons hold q, by simp only [Walk.length_cons]; omega⟩)
    · have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
        simpa only [Sym2.eq_iff] using he
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨.nil,by simp⟩)
      · exact Or.inr (Or.inr ⟨.nil,by simp⟩)

/-- In a graph of girth at least L, an alternate path across an old edge
has length at least L-1. This is precisely the nonbad-edge input to the
matching transposition argument. -/
theorem girth_alternate_lower (L : ℕ) (hG : (L : ℕ∞) ≤ G.egirth)
    (hxy : G.Adj x y) (p : (G.deleteEdges {s(x,y)}).Walk x y) :
    L ≤ p.length + 1 := by
  classical
  let hp := p.mapLe (SimpleGraph.deleteEdges_le {s(x,y)})
  have he : s(x,y) ∉ hp.edges := by
    intro he
    have hmem : s(x,y) ∈ p.edges := by simpa only [hp,Walk.edges_mapLe_eq_edges] using he
    have hg := p.edges_subset_edgeSet hmem
    simp at hg
  have hc := hp.toPath.cons_isCycle hxy.symm (by
    rw [Sym2.eq_swap]
    exact fun h => he (Walk.edges_toPath_subset_edges hp h))
  have hh := SimpleGraph.le_egirth.mp hG y (.cons hxy.symm hp.toPath) hc
  have hlen := hp.length_bypass_le_length
  have hh' : L ≤ hp.bypass.length + 1 := by exact_mod_cast hh
  simpa only [hp,Walk.length_mapLe] using hh'.trans (Nat.add_le_add_right hlen 1)

/-- Two-switching in a simple graph: delete xy and uz, then add xz and uy.
The distance condition is the manuscript's separation of the two endpoint
sets. All previous prescribed edges survive provided neither deleted edge
was among those prescriptions. -/
theorem girth_switch (L : ℕ) {x y u z : V}
    (hG : (L : ℕ∞) ≤ G.egirth) (huz : G.Adj u z)
    (hfar : ∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
      ∀ p : G.Walk a b, 2 * L < p.length) :
    (L : ℕ∞) ≤
      (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y).egirth := by
  let H := G.deleteEdges {s(x,y),s(u,z)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hH : (L : ℕ∞) ≤ H.egirth := hG.trans (SimpleGraph.egirth_anti hHG)
  have hxz (p : H.Walk x z) : L ≤ p.length + 1 := by
    have hf := hfar x (by simp) z (by simp) (p.mapLe hHG)
    simp only [Walk.length_mapLe] at hf
    omega
  have hg1 := girth_addEdge L hH hxz
  apply girth_addEdge L hg1
  intro p
  rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
  · have hf := hfar y (by simp) u (by simp) ((q.mapLe hHG).reverse)
    simp only [Walk.length_reverse,Walk.length_mapLe] at hf
    omega
  · have hf := hfar x (by simp) u (by simp) ((q.mapLe hHG).reverse)
    simp only [Walk.length_reverse,Walk.length_mapLe] at hf
    omega
  · have hdel : H ≤ G.deleteEdges {s(u,z)} := by
      apply SimpleGraph.deleteEdges_anti
      simp only [Set.singleton_subset_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
      simp
    have hl := girth_alternate_lower L hG huz (q.mapLe hdel)
    simp only [Walk.length_mapLe] at hl
    omega

/-- Short cycles in an edge-adjoined graph descend to the old graph whenever
there is no short alternate path. This needs no girth assumption on the old
graph, and so also applies during the initial bad-edge repair algorithm. -/
theorem short_cycle_descends_add (L : ℕ)
    (hx : ∀ p : G.Walk x y, L ≤ p.length + 1)
    (p : (addEdge G x y).Walk a a) (hp : p.IsCycle) (hlen : p.length < L) :
    ∃ q : G.Walk a a, q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length := by
  classical
  have he : s(x,y) ∉ p.edges := by
    intro he
    obtain ⟨u,v,q,huv,hqe,hql⟩ := alternate_walk p hp.isTrail _ he
    obtain ⟨q',hq'⟩ := transfer_addEdge q hqe
    have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa only [Sym2.eq_iff] using huv
    have hl : L ≤ q'.length + 1 := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx q'
      · simpa only [Walk.length_reverse] using hx q'.reverse
    omega
  have ht : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
    intro e he'
    have hg := p.edges_subset_edgeSet he'
    simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
    rcases hg with hg | ⟨rfl,_⟩
    · exact hg
    · exact False.elim (he he')
  exact ⟨p.transfer G ht,hp.transfer ht,Walk.edges_transfer ..,Walk.length_transfer ..⟩

/-- At the shortest-cycle threshold, no nonbadness requirement is needed
on the auxiliary edge: a new cycle using both new edges is strictly longer
than the old girth. This permits deterministic girth repair. -/
theorem shortest_cycle_descends_switch (L : ℕ) {x y u z : V}
    (hG : (L : ℕ∞) ≤ G.egirth) (huz : G.Adj u z)
    (hfar : ∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
      ∀ p : G.Walk a b, 2 * (L+1) < p.length)
    (p : (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y).Walk a a)
    (hp : p.IsCycle) (hlen : p.length < L+1) :
    ∃ q : (G.deleteEdges {s(x,y),s(u,z)}).Walk a a,
      q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length := by
  let H := G.deleteEdges {s(x,y),s(u,z)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hxz (p : H.Walk x z) : L+1 ≤ p.length + 1 := by
    have hf := hfar x (by simp) z (by simp) (p.mapLe hHG)
    simp only [Walk.length_mapLe] at hf
    omega
  have huy (p : (addEdge H x z).Walk u y) : L+1 ≤ p.length + 1 := by
    rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
    · have hf := hfar y (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hf := hfar x (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hdel : H ≤ G.deleteEdges {s(u,z)} := by
        apply SimpleGraph.deleteEdges_anti
        simp
      have hl := girth_alternate_lower L hG huz (q.mapLe hdel)
      simp only [Walk.length_mapLe] at hl
      omega
  obtain ⟨q,hq,hqe,hql⟩ := short_cycle_descends_add (L+1) huy p hp hlen
  obtain ⟨q',hq',hq'e,hq'l⟩ := short_cycle_descends_add (L+1) hxz q hq (by omega)
  exact ⟨q',hq',hq'e.trans hqe,hq'l.trans hql⟩

/-- The exact set minimized by the finite repair argument. -/
def badEdges (G : SimpleGraph V) (L : ℕ) : Set (Sym2 V) :=
  {e | ∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ p.length < L ∧ e ∈ p.edges}

/-- Edgewise transfer of short cycles strictly reduces the bad edge set
as soon as a specified old bad edge has been deleted. -/
theorem badEdges_strict {L : ℕ} [Fintype V] (e : Sym2 V) (he : e ∈ badEdges G L)
    (hdesc : ∀ a (p : H.Walk a a), p.IsCycle → p.length < L →
      ∃ q : G.Walk a a, q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length)
    (hdel : e ∉ badEdges H L) :
    (badEdges H L).toFinite.toFinset.card < (badEdges G L).toFinite.toFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro f hf
    have hf' : f ∈ badEdges H L := by simpa using hf
    obtain ⟨a,p,hp,hl,hf'⟩ := hf'
    obtain ⟨q,hq,hqe,hql⟩ := hdesc a p hp hl
    simpa using (show f ∈ badEdges G L from ⟨a,q,hq,by omega,hqe ▸ hf'⟩)
  · intro heq
    have heH : e ∈ (badEdges H L).toFinite.toFinset := by
      rw [heq]
      simpa using he
    have heH' : e ∈ badEdges H L := by simpa using heH
    exact hdel heH'

/-- Finite extremal repair raises the girth by one. Unlike the manuscript's
probabilistic initialization, this argument only needs the uniform far-edge
supply; all objects and the final girth condition are unchanged. -/
theorem girth_improve_one [Fintype V] (L : ℕ) (P : SimpleGraph V → Prop)
    (hne : ∃ G, P G ∧ (L : ℕ∞) ≤ G.egirth)
    (hswitch : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
          ∀ p : G.Walk a b, 2 * (L+1) < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y)) :
    ∃ G, P G ∧ ((L+1 : ℕ) : ℕ∞) ≤ G.egirth := by
  classical
  let S : Set (SimpleGraph V) := {G | P G ∧ (L : ℕ∞) ≤ G.egirth}
  obtain ⟨G,hGP,hmin⟩ := S.exists_min_image
    (fun G => (badEdges G (L+1)).toFinite.toFinset.card) S.toFinite hne
  refine ⟨G,hGP.1,?_⟩
  by_contra hn
  rw [SimpleGraph.le_egirth] at hn
  push Not at hn
  obtain ⟨a,p,hp,hl⟩ := hn
  have hlen : p.length < L+1 := by exact_mod_cast hl
  obtain ⟨x,y,u,z,he,huz,hfar,hP⟩ := hswitch G hGP.1 a p hp
  let e := s(x,y)
  let H := addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y
  have hdesc (a : V) (q : H.Walk a a) (hq : q.IsCycle) (hl : q.length < L+1) :=
    shortest_cycle_descends_switch L hGP.2 huz hfar q hq hl
  have hstrict : (badEdges H (L+1)).toFinite.toFinset.card <
      (badEdges G (L+1)).toFinite.toFinset.card := by
    apply badEdges_strict e ⟨a,p,hp,hlen,he⟩
    · intro a q hq hl
      obtain ⟨q',hq',hqe,hql⟩ := hdesc a q hq hl
      exact ⟨q'.mapLe (SimpleGraph.deleteEdges_le _), hq'.mapLe _,
        (Walk.edges_mapLe_eq_edges ..).trans hqe,(Walk.length_mapLe ..).trans hql⟩
    · rintro ⟨a,q,hq,hl,heq⟩
      obtain ⟨q',hq',hqe,hql⟩ := hdesc a q hq hl
      have hg := q'.edges_subset_edgeSet (hqe ▸ heq)
      change s(x,y) ∈ (G.deleteEdges {s(x,y),s(u,z)}).edgeSet at hg
      simp at hg
  have hHg : (L : ℕ∞) ≤ H.egirth := girth_switch L hGP.2 huz (by
    intro a ha b hb q
    have hh := hfar a ha b hb q
    omega)
  exact (not_lt_of_ge (hmin H ⟨hP,hHg⟩)) hstrict

/-- Arbitrarily specified finite girth follows by finitely many exact
transpositions if the family has a uniform distant auxiliary edge supply. -/
theorem exists_large_girth [Fintype V] (N : ℕ) (P : SimpleGraph V → Prop)
    (hne : ∃ G, P G)
    (hswitch : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
          ∀ p : G.Walk a b, 2 * N < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y)) :
    ∃ G, P G ∧ (N : ℕ∞) ≤ G.egirth := by
  have hstep : ∀ k ≤ N, ∃ G, P G ∧ (k : ℕ∞) ≤ G.egirth := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨G,hG⟩ := hne
      exact ⟨G,hG,zero_le⟩
    | succ k ih =>
      intro hk
      apply girth_improve_one k P (ih (by omega))
      intro G hG a p hp
      obtain ⟨x,y,u,z,he,huz,hfar,hP⟩ := hswitch G hG a p hp
      refine ⟨x,y,u,z,he,huz,?_,hP⟩
      intro a ha b hb p
      have hf := hfar a ha b hb p
      omega
  exact hstep N le_rfl

end TorsionFreeZeroDivisors.GirthSwitch

/-! ### Typed matching families have nonempty large-girth spaces. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedCycles
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

end TorsionFreeZeroDivisors.WeightedCycles
namespace TorsionFreeZeroDivisors.WeightedMoore
open scoped BigOperators

instance {D : Type*} [Fintype D] (k : ℕ) : Fintype (Chain D k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype D)
  | succ k ih => exact inferInstanceAs (Fintype (D × Chain D k))

def last {D : Type*} : {k : ℕ} → Chain D k → D
  | 0, p => p
  | _+1, p => last p.2

variable {D : Type*} [Fintype D] (T : D → D → ℝ)

variable {T}

namespace PortWalk

variable {V : Type*} (origin : D → V) (rev : D → D)
    (hinv : Function.Involutive rev)

open scoped Classical

include hinv

end PortWalk

end TorsionFreeZeroDivisors.WeightedMoore

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedPortMoore
open SimpleGraph WeightedMoore PortSubdivision
variable {V D : Type*} (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.WeightedPortMoore

namespace TorsionFreeZeroDivisors.ChainSuppression
open Function
open scoped Classical

variable {D : Type*} (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

include hσ hτ

variable [Finite D]

/-- Each directed edge can be traversed at most once among all oriented
maximal chains. This is the exact disjoint-interior count, not a bound supplied
as an extra hypothesis. -/
lemma chain_dart_injective :
    Injective (fun p : (x : {x : D // τ x=x}) × Fin (length σ τ hσ hτ x.val x.property) =>
      (next σ τ)^[p.2.val] p.1.val) := by
  intro ⟨x,i⟩ ⟨y,j⟩ he
  have hone (x y : {x : D // τ x=x})
      (i : Fin (length σ τ hσ hτ x.val x.property))
      (j : Fin (length σ τ hσ hτ y.val y.property))
      (hij : i.val ≤ j.val)
      (he : (next σ τ)^[i.val] x.val=(next σ τ)^[j.val] y.val) :
      x=y ∧ i.val=j.val := by
    have hji : j.val=i.val+(j.val-i.val) := by omega
    rw [hji,iterate_add_apply] at he
    have hr := ((next_injective σ τ hσ hτ).iterate i.val) he
    have hzero : j.val-i.val=0 := by
      by_contra hz
      have hf : τ ((next σ τ)^[j.val-i.val] y.val)=(next σ τ)^[j.val-i.val] y.val := by
        rw [← hr]; exact x.property
      exact no_internal_mark σ τ hσ hτ y.val y.property (Nat.pos_of_ne_zero hz)
        (by omega) hf
    have hexy : x=y := by
      apply Subtype.ext
      simpa only [hzero,iterate_zero,id_eq] using hr
    exact ⟨hexy,by omega⟩
  have hxy : x=y ∧ i.val=j.val := by
    rcases le_total i.val j.val with hij | hji
    · exact hone x y i j hij he
    · obtain ⟨hexy,hij⟩ := hone y x j i hji he.symm
      exact ⟨hexy.symm,hij.symm⟩
  obtain ⟨rfl,hij⟩ := hxy
  congr 1
  exact Fin.ext hij

end TorsionFreeZeroDivisors.ChainSuppression

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.DegreeTwoSuppression
open Function
open scoped Classical
open TorsionFreeZeroDivisors ChainSuppression PortSubdivision
variable {V D : Type*} [Fintype D]

variable (o : D → V) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out o v).card=2)

lemma turn_origin (d : D) : o (turn o mark h2 d)=o d := by
  by_cases hd : mark (o d)
  · rw [turn_of_mark o mark h2 d hd]
  · exact (turn_of_unmarked o mark h2 d hd).1

lemma turn_fixed_iff (d : D) : turn o mark h2 d=d ↔ mark (o d) := by
  constructor
  · intro he
    by_contra hd
    exact (turn_of_unmarked o mark h2 d hd).2 he
  · exact turn_of_mark o mark h2 d

lemma chainLength_pos (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) : 0 < chainLength Γ mark h2 d :=
  length_pos _ _ _ _ _ _

lemma chainLength_reverse (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) :
    chainLength Γ mark h2 ((suppressed Γ mark h2).reverse d)=chainLength Γ mark h2 d :=
  length_endpoint _ _ _ _ _

end TorsionFreeZeroDivisors.DegreeTwoSuppression

namespace TorsionFreeZeroDivisors.SuppressedMoore
open Function SimpleGraph
open scoped Classical
open TorsionFreeZeroDivisors PortSubdivision WeightedMoore
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)

local notation "τ" => DegreeTwoSuppression.turn Γ.origin mark h2
local notation "hτ" => DegreeTwoSuppression.turn_involutive Γ.origin mark h2
local notation "F" => ChainSuppression.next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "Γ'" => DegreeTwoSuppression.suppressed Γ mark h2
local notation "len" => DegreeTwoSuppression.chainLength Γ mark h2

omit [Fintype D] in
@[simp] lemma last_iterChain (f : D → D) (n : ℕ) (x : D) :
    last (iterChain f n x)=f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change last (iterChain f n (f x))=f^[n+1] x
    rw [ih,iterate_succ_apply]

lemma chain_last (d : B) : Γ.reverse (last (iterChain F (len d-1) d.val)) = ((Γ').reverse d).val := by
  rw [last_iterChain]
  have hf := ((Γ').reverse d).property
  change τ (F^[len d] d.val)=F^[len d] d.val at hf
  have hk : len d=(len d-1)+1 := by
    have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
    omega
  conv_lhs at hf => rw [hk,iterate_succ_apply']
  change τ (τ (Γ.reverse (F^[len d-1] d.val)))=F^[len d] d.val at hf
  rw [hτ] at hf
  exact hf

end TorsionFreeZeroDivisors.SuppressedMoore

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainCoverage
open Function ChainSuppression
open scoped Classical
variable {D : Type*} [Finite D] (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

end TorsionFreeZeroDivisors.ChainCoverage

namespace TorsionFreeZeroDivisors.ActualMarkedChains
open Function PortSubdivision ChainSuppression DegreeTwoSuppression ChainCoverage
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)

end TorsionFreeZeroDivisors.ActualMarkedChains

namespace TorsionFreeZeroDivisors.MarkedChainBound
open PortSubdivision DegreeTwoSuppression
open scoped Classical BigOperators
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.MarkedChainBound

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

omit [Fintype D] in
lemma outWord_length {k : ℕ} (p : Chain D k) : (outWord p).length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [outWord,List.length_cons,Nat.succ_eq_add_one,Nat.add_right_cancel_iff] using ih p.2

lemma word_length (d : B) : (word Γ mark h2 d).length=len d := by
  rw [word,outWord_length]
  have h := chainLength_pos Γ mark h2 d
  omega

omit [Fintype D] in
/-- Enumerating a chain lists precisely the forward iterates before its first mark. -/
lemma outWord_iterChain (f : D → D) (n : ℕ) (x : D) :
    outWord (iterChain f n x) = (List.range (n+1)).map (fun i => f^[i] x) := by
  induction n generalizing x with
  | zero => simp [iterChain,outWord]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [iterChain,outWord,ih,List.map_cons,List.map_map,iterate_zero,id_eq]
    congr 1

lemma word_eq_range (d : B) :
    word Γ mark h2 d = (List.range (len d)).map (fun i => F^[i] d.val) := by
  rw [word,outWord_iterChain]
  have h := chainLength_pos Γ mark h2 d
  congr 2
  omega

lemma mem_word_iff (d : B) (x : D) :
    x∈word Γ mark h2 d ↔ ∃ i : Fin (len d), F^[i.val] d.val=x := by
  rw [word_eq_range,List.mem_map]
  constructor
  · rintro ⟨i,hi,hx⟩
    exact ⟨⟨i,List.mem_range.mp hi⟩,hx⟩
  · rintro ⟨i,hx⟩
    exact ⟨i.val,List.mem_range.mpr i.isLt,hx⟩

lemma words_disjoint {d e : B} (hne : d≠e) :
    List.Disjoint (word Γ mark h2 d) (word Γ mark h2 e) := by
  intro x hx hy
  obtain ⟨i,hi⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  obtain ⟨j,hj⟩ := (mem_word_iff Γ mark h2 e x).mp hy
  have h := chain_dart_injective Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (a₁ := ⟨d,i⟩) (a₂ := ⟨e,j⟩) (hi.trans hj.symm)
  exact hne (congrArg Sigma.fst h)

end TorsionFreeZeroDivisors.ChainPaths

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BlockPropagation

open scoped BigOperators

structure Skeleton (I : Type*) where
  root : I
  parent : I → I
  rank : I → ℕ
  decreasing : ∀ i, i ≠ root → rank (parent i) < rank i

/-- A connected comparison graph supplies a decreasing parent system, with
any chosen block as root (in particular the minimizer of its weight bin). -/
theorem exists_skeleton {I : Type*} (G : SimpleGraph I) (hc : G.Connected) (r : I) :
    ∃ S : Skeleton I, S.root = r ∧ ∀ i, i ≠ r → G.Adj i (S.parent i) := by
  classical
  have hn (i : I) (hi : i ≠ r) :
      ∃ j, G.Adj i j ∧ G.dist j r < G.dist i r := by
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist i r
    cases p with
    | nil => exact False.elim (hi rfl)
    | @cons a b c hab p =>
      refine ⟨b, hab, ?_⟩
      have hle := G.dist_le p
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega
  let parent := fun i => if hi : i = r then r else (hn i hi).choose
  refine ⟨⟨r, parent, fun i => G.dist i r, ?_⟩, rfl, ?_⟩
  · intro i hi
    dsimp [parent]
    rw [dif_neg hi]
    exact (hn i hi).choose_spec.2
  · intro i hi
    dsimp [parent]
    rw [dif_neg hi]
    exact (hn i hi).choose_spec.1

namespace Skeleton

variable {I T : Type*} (S : Skeleton I) (h : I → ℕ)
    (known : (i : I) → Finset (Fin (h i)))
    (determine : (i : I) → Fin (h i) → (Fin (h (S.parent i)) → T) → T)

abbrev Assignment := (i : I) → Fin (h i) → T

def Consistent (w : Assignment h (T := T)) : Prop :=
  ∀ i, i ≠ S.root → ∀ k ∈ known i, w i k = determine i k (w (S.parent i))

abbrev FreePosition := {p : (i : I) × Fin (h i) // p.1 ≠ S.root ∧ p.2 ∉ known p.1}

/-- The omitted coordinates plus the root word determine every full word. -/
theorem assignment_ext {w v : Assignment h (T := T)}
    (hw : S.Consistent h known determine w) (hv : S.Consistent h known determine v)
    (hroot : w S.root = v S.root)
    (hfree : ∀ p : S.FreePosition h known, w p.val.1 p.val.2 = v p.val.1 p.val.2) : w = v := by
  have hall (n : ℕ) : ∀ i, S.rank i = n → w i = v i := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      by_cases hir : i = S.root
      · subst i
        exact hroot
      · funext k
        by_cases hk : k ∈ known i
        · rw [hw i hir k hk, hv i hir k hk]
          have hp : S.rank (S.parent i) < n := hi ▸ S.decreasing i hir
          rw [ih _ hp (S.parent i) rfl]
        · exact hfree ⟨⟨i,k⟩,hir,hk⟩
  funext i
  exact hall (S.rank i) i rfl

variable [Fintype I] [Fintype T] [DecidableEq I]

/-- Exact number of unrecorded letters after the tree comparisons. -/
theorem card_freePositions :
    Nat.card (S.FreePosition h known) =
      ∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card) := by
  classical
  let e : S.FreePosition h known ≃
      (i : {i : I // i ≠ S.root}) × {k : Fin (h i.val) // k ∉ known i.val} :=
    { toFun := fun p => ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩⟩
      invFun := fun p => ⟨⟨p.1.val,p.2.val⟩,p.1.property,p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-- Choose actual root words from R, then at most |T| choices per omitted
coordinate. The remaining coordinates are forced by the comparisons. -/
theorem card_assignments (R : Finset (Fin (h S.root) → T)) :
    Nat.card {w : Assignment h (T := T) //
      S.Consistent h known determine w ∧ w S.root ∈ R} ≤
      R.card * (Fintype.card T) ^
        (∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card)) := by
  classical
  let encode : {w : Assignment h (T := T) //
        S.Consistent h known determine w ∧ w S.root ∈ R} →
      R × (S.FreePosition h known → T) := fun w =>
    (⟨w.val S.root,w.property.2⟩,fun p => w.val p.val.1 p.val.2)
  have henc : Function.Injective encode := by
    intro w v he
    apply Subtype.ext
    apply S.assignment_ext h known determine w.property.1 v.property.1
    · exact congrArg (fun p => p.1.val) he
    · intro p
      exact congrFun (congrArg Prod.snd he) p
  have hc := Fintype.card_le_of_injective encode henc
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun] at hc
  have he : Fintype.card (S.FreePosition h known) =
      ∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card) := by
    simpa only [Nat.card_eq_fintype_card] using S.card_freePositions h known
  simpa only [Nat.card_eq_fintype_card, he] using hc

end Skeleton
end TorsionFreeZeroDivisors.BlockPropagation

/-! Label projection along connected substring links.
A link determines a specified subset of one block from positions in its
partner word, via a letter equivalence such as identity or inversion.
No embedding of inactive graph vertices is requested or assumed. -/
namespace TorsionFreeZeroDivisors.StageLabels

section
open scoped Classical BigOperators
open BlockPropagation

variable {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]

/-- A finite directed presentation of substring links. Both directions of
an actual interval-isometry link may be included; extra constraints only
reduce the set of feasible strings. -/
structure Links (h : I → ℕ) where
  graph : SimpleGraph I
  known : (i j : I) → Finset (Fin (h i))
  source : (i j : I) → known i j → Fin (h j)
  symbol : I → I → (T ≃ T)

namespace Links
variable {h : I → ℕ} (L : Links (T := T) h)

abbrev Word := (i : I) → Fin (h i) → T

def Consistent (w : Word (T := T) (h := h)) : Prop :=
  ∀ i j, L.graph.Adj i j → ∀ k : L.known i j,
    w i k.val = L.symbol i j (w j (L.source i j k))

abbrev RootedWords (r : I) (R : Finset (Fin (h r) → T)) :=
  {w : Word (T := T) (h := h) // L.Consistent w ∧ w r ∈ R}

/-- Full strings on a connected link component, with a chosen root, are
bounded by the root choices times one alphabet choice per missing position. -/
theorem connected_count (hc : L.graph.Connected) (r : I)
    (R : Finset (Fin (h r) → T)) (e : ℕ)
    (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e) :
    Fintype.card (L.RootedWords r R) ≤
      R.card * (Fintype.card T)^(e*(Fintype.card I-1)) := by
  obtain ⟨S,hr,hparent⟩ := exists_skeleton L.graph hc r
  subst r
  let known := fun i => L.known i (S.parent i)
  let determine := fun i (k : Fin (h i)) (w : Fin (h (S.parent i)) → T) =>
    if hk : k ∈ known i then L.symbol i (S.parent i) (w (L.source i (S.parent i) ⟨k,hk⟩))
    else Classical.choice (inferInstance : Nonempty T)
  let forget : L.RootedWords S.root R →
      {w : Skeleton.Assignment h (T := T) // S.Consistent h known determine w ∧ w S.root ∈ R} :=
    fun w => ⟨w.val,by
      constructor
      · intro i hi k hk
        dsimp [determine]
        rw [dif_pos hk]
        exact w.property.1 i (S.parent i) (hparent i hi) ⟨k,hk⟩
      · exact w.property.2⟩
  have hf : Function.Injective forget := by
    intro a b heq
    apply Subtype.ext
    exact congrArg (fun q : {w : Skeleton.Assignment h (T := T) //
      S.Consistent h known determine w ∧ w S.root ∈ R} => q.val) heq
  have hk : (∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card)) ≤
      e*(Fintype.card I-1) := by
    calc
      _ ≤ ∑ _i : {i : I // i ≠ S.root}, e := Finset.sum_le_sum (fun i _ =>
        he i.val (S.parent i.val) (hparent i.val i.property))
      _ = e*(Fintype.card I-1) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_subtype_compl]
        have hr : Fintype.card {i : I // i = S.root} = 1 := by simp
        rw [hr,mul_comm]
        rfl
  calc
    _ ≤ Fintype.card {w : Skeleton.Assignment h (T := T) //
        S.Consistent h known determine w ∧ w S.root ∈ R} :=
      Fintype.card_le_of_injective forget hf
    _ ≤ R.card * (Fintype.card T)^
        (∑ i : {i : I // i ≠ S.root}, (h i.val - (known i.val).card)) := by
      simpa only [Nat.card_eq_fintype_card] using S.card_assignments h known determine R
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Fintype.card_pos hk)

end Links

variable {C : Type*} [Fintype C] (color : I → C) (h : I → ℕ)

abbrev Fiber (c : C) := {i : I // color i = c}
abbrev PieceWord (c : C) := (i : Fiber color c) → Fin (h i.val) → T

def restrictWord (w : (i : I) → Fin (h i) → T) (c : C) : PieceWord (T := T) color h c :=
  fun i => w i.val

def activeComponents (A : Finset I) : Finset C :=
  A.image color

def stageWords (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop) :
    Finset ((i : A) → Fin (h i.val) → T) :=
  (Finset.univ.filter P).image (fun w i => w i.val)

omit [Nonempty T] [Fintype C] in
/-- Restriction to active blocks is bounded by complete strings only on the
components they meet. The representative root of a component need not be
active: the witness is a *string*, not an embedding in a sampled graph. -/
theorem projection_count (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop)
    (Q : (c : C) → PieceWord (T := T) color h c → Prop)
    (hQ : ∀ w, P w → ∀ c ∈ activeComponents color A, Q c (restrictWord color h w c)) :
    (stageWords h A P).card ≤
      ∏ c : activeComponents color A, Fintype.card {w : PieceWord (T := T) color h c.val // Q c.val w} := by
  have hs (w : stageWords h A P) :
      ∃ W : (i : I) → Fin (h i) → T, P W ∧ (fun i : A => W i.val) = w.val := by
    obtain ⟨W,hW,hw⟩ := Finset.mem_image.mp w.property
    exact ⟨W,(Finset.mem_filter.mp hW).2,hw⟩
  let full (w : stageWords h A P) := (hs w).choose
  have full_spec (w : stageWords h A P) :
      P (full w) ∧ (fun i : A => full w i.val) = w.val := (hs w).choose_spec
  let encode (w : stageWords h A P) : (c : activeComponents color A) →
      {W : PieceWord (T := T) color h c.val // Q c.val W} :=
    fun c => ⟨restrictWord color h (full w) c.val,hQ _ (full_spec w).1 c.val c.property⟩
  have he : Function.Injective encode := by
    intro w v heq
    apply Subtype.ext
    funext i
    let c : activeComponents color A := ⟨color i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
    have h1 := congrFun (congrArg (fun f => (f c).val) heq) (⟨i.val,rfl⟩ : Fiber color c.val)
    change full w i.val = full v i.val at h1
    rw [← (congrFun (full_spec w).2 i),← (congrFun (full_spec v).2 i)]
    exact h1
  have hc := Fintype.card_le_of_injective encode he
  simpa only [Fintype.card_coe,Fintype.card_pi] using hc

end

open scoped Classical BigOperators
variable {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]
variable {h : I → ℕ} (L : Links (T := T) h)

namespace Links

def component (c : L.graph.ConnectedComponent) : Links (T := T) (fun i : c => h i.val) where
  graph := c.toSimpleGraph
  known i j := L.known i.val j.val
  source i j := L.source i.val j.val
  symbol i j := L.symbol i.val j.val

omit [Fintype I] [Fintype T] [Nonempty T] in
theorem restrict_consistent {w : (i : I) → Fin (h i) → T} (hw : L.Consistent w)
    (c : L.graph.ConnectedComponent) :
    (L.component c).Consistent (fun i => w i.val) := by
  intro i j hij k
  exact hw i.val j.val hij k

/-- Exact local bound on one actual connected component; its root is arbitrary. -/
theorem component_count (c : L.graph.ConnectedComponent) (r : c)
    (R : Finset (Fin (h r.val) → T)) (e : ℕ)
    (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e) :
    Fintype.card ((L.component c).RootedWords r R) ≤
      R.card * (Fintype.card T)^(e*(Fintype.card c-1)) := by
  have hc : (L.component c).graph.Connected := c.connected_toSimpleGraph
  have hh := (L.component c).connected_count hc r R e
    (fun i j hij => he i.val j.val hij)
  simpa only [← Nat.card_eq_fintype_card] using hh

omit [Fintype T] [Nonempty T] in
/-- Sum of sizes only over components met by the stage. -/
theorem active_component_size (A : Finset I) :
    (∑ c : activeComponents L.graph.connectedComponentMk A, Fintype.card c.val) ≤
      Fintype.card I := by
  let f : (c : activeComponents L.graph.connectedComponentMk A) × c.val → I :=
    fun x => x.2.val
  have hf : Function.Injective f := by
    rintro ⟨c,i⟩ ⟨d,j⟩ hij
    change i.val = j.val at hij
    have hcd : c = d := Subtype.ext (i.property.symm.trans (hij ▸ j.property))
    subst d
    have hi : i = j := Subtype.ext hij
    subst j
    rfl
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective f hf

/-- Completing strings on each active link component before projection gives
an exponential stage bound. No vertices of an inactive chain are embedded. -/
theorem stage_exp (A : Finset I)
    (r : (c : L.graph.ConnectedComponent) → c)
    (R : (c : L.graph.ConnectedComponent) → Finset (Fin (h (r c).val) → T))
    (P : ((i : I) → Fin (h i) → T) → Prop)
    (hP : ∀ w, P w → L.Consistent w)
    (hroot : ∀ w, P w → ∀ c, w (r c).val ∈ R c)
    (e : ℕ) (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e)
    (cost : L.graph.ConnectedComponent → ℝ)
    (hcost : ∀ c, ((R c).card : ℝ) ≤ Real.exp (cost c)) :
    ((stageWords h A P).card : ℝ) ≤
      Real.exp ((∑ c : activeComponents L.graph.connectedComponentMk A, cost c.val) +
        (e : ℝ) * Fintype.card I * Real.log (Fintype.card T)) := by
  let C := activeComponents L.graph.connectedComponentMk A
  have hp : (stageWords h A P).card ≤
      ∏ c : C, Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) := by
    have hh := projection_count L.graph.connectedComponentMk h A P
      (fun c w => (L.component c).Consistent w ∧ w (r c) ∈ R c)
      (fun w hw c _ => ⟨L.restrict_consistent (hP w hw) c, hroot w hw c⟩)
    convert hh using 1
    apply congrArg
    funext c
    simp only [← Nat.card_eq_fintype_card]
    rfl
  have ha : 0 < (Fintype.card T : ℝ) := by exact_mod_cast Fintype.card_pos
  have halog : 0 ≤ Real.log (Fintype.card T) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := T))
  have hcard (c : C) :
      (Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) : ℝ) ≤
        Real.exp (cost c.val + (e : ℝ) * Fintype.card c.val * Real.log (Fintype.card T)) := by
    have hn := L.component_count c.val (r c.val) (R c.val) e he
    have hn' : (Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) : ℝ) ≤
        ((R c.val).card : ℝ) * (Fintype.card T : ℝ)^(e*(Fintype.card c.val-1)) := by exact_mod_cast hn
    calc
      _ ≤ ((R c.val).card : ℝ) * (Fintype.card T : ℝ)^(e*(Fintype.card c.val-1)) := hn'
      _ ≤ Real.exp (cost c.val) * (Fintype.card T : ℝ)^(e*(Fintype.card c.val-1)) :=
        mul_le_mul_of_nonneg_right (hcost _) (pow_nonneg ha.le _)
      _ = Real.exp (cost c.val + (e*(Fintype.card c.val-1) : ℕ) * Real.log (Fintype.card T)) := by
        rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log ha]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_right _ halog
        rw [Nat.cast_mul]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg e)
        exact_mod_cast Nat.sub_le (Fintype.card c.val) 1
  calc
    _ ≤ (∏ c : C, (Fintype.card ((L.component c.val).RootedWords (r c.val) (R c.val)) : ℝ)) := by
      exact_mod_cast hp
    _ ≤ ∏ c : C, Real.exp (cost c.val + (e : ℝ)*Fintype.card c.val*Real.log (Fintype.card T)) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun component _ => hcard component)
    _ = Real.exp ((∑ c : C, cost c.val) +
        (e : ℝ)*(∑ c : C, (Fintype.card c.val : ℝ))*Real.log (Fintype.card T)) := by
      rw [← Real.exp_sum,Finset.sum_add_distrib]
      congr 1
      simp only [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right _ halog
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg e)
      exact_mod_cast L.active_component_size A

end Links
end TorsionFreeZeroDivisors.StageLabels

/-! The link constraints are now extracted from the actual occurrence
matching, rather than supplied as an unexplained propagation hypothesis. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchedLabels
open scoped Classical
open OccurrenceMatching StageLabels
variable {Ω B E I A : Type*}
variable (D : Data (Ω := Ω) (B := B) (E := E)) (color : B → I)
variable (h : I → ℕ) (coordinate : ∀ b, D.positions b ≃ Fin (h (color b)))
variable (symbol : E → (A ≃ A))

def graph : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ b, color b = i ∧ color (D.matching.partner b) = j
  symm := ⟨by
    rintro i j ⟨hne,b,hi,hj⟩
    exact ⟨hne.symm,D.matching.partner b,hj,by rw [D.matching.involutive]; exact hi⟩⟩
  loopless := ⟨fun i hh => hh.1 rfl⟩

structure Witness (i j : I) where
  origin : B
  origin_color : color origin = i
  target_color : color (D.matching.partner origin) = j
  side : E
  joined : (D.positions origin).card < 2*(D.slice side origin (D.matching.partner origin)).card ∧
    (D.positions (D.matching.partner origin)).card < 2*(D.slice side origin (D.matching.partner origin)).card ∧
    (D.positions origin).card ≤ (D.slice side origin (D.matching.partner origin)).card+D.error ∧
    (D.positions (D.matching.partner origin)).card ≤
      (D.slice side origin (D.matching.partner origin)).card+D.error

theorem exists_witness {i j : I} (hadj : (graph D color).Adj i j) :
    Nonempty (Witness D color i j) := by
  obtain ⟨hne,b,hi,hj⟩ := hadj
  have hb : D.matching.partner b ≠ b := by
    intro he
    apply hne
    rw [he] at hj
    exact hi.symm.trans hj
  obtain ⟨p,hp⟩ := (D.matched_iff b).mp hb
  have he := D.partner_spec hp
  change D.matching.partner b = p at he
  obtain ⟨e,he'⟩ := hp
  exact ⟨⟨b,hi,hj,e,by simpa only [he] using he'⟩⟩

namespace Witness
variable {D color} {i j : I} (W : Witness D color i j)

def domain : Finset Ω := D.slice W.side W.origin (D.matching.partner W.origin)

def originCoordinate : D.positions W.origin ≃ Fin (h i) :=
  (coordinate W.origin).trans (finCongr (congrArg h W.origin_color))

def targetCoordinate : D.positions (D.matching.partner W.origin) ≃ Fin (h j) :=
  (coordinate (D.matching.partner W.origin)).trans (finCongr (congrArg h W.target_color))

def includeDomain : W.domain ↪ D.positions W.origin where
  toFun x := ⟨x.val,(D.slice_mem.mp x.property).1⟩
  inj' := by
    intro u v he
    apply Subtype.ext
    exact congrArg (fun z : D.positions W.origin => z.val) he

def compareTarget (x : W.domain) : D.positions (D.matching.partner W.origin) :=
  ⟨D.pairing.partner x.val,(D.slice_mem.mp x.property).2.2⟩

def known : Finset (Fin (h i)) :=
  Finset.univ.map (W.includeDomain.trans (W.originCoordinate h coordinate).toEmbedding)

theorem known_card : (W.known h coordinate).card = W.domain.card := by
  simp [known]

def recover (x : W.known h coordinate) : W.domain :=
  Classical.choose (Finset.mem_map.mp x.property)

theorem recover_spec (x : W.known h coordinate) :
    W.originCoordinate h coordinate (W.includeDomain (W.recover h coordinate x)) = x.val :=
  (Classical.choose_spec (Finset.mem_map.mp x.property)).2

def source (x : W.known h coordinate) : Fin (h j) :=
  W.targetCoordinate h coordinate (W.compareTarget (W.recover h coordinate x))

theorem deficit : h i - (W.known h coordinate).card ≤ D.error := by
  rw [W.known_card]
  have hc : h i = (D.positions W.origin).card := by
    simpa using (Fintype.card_congr (W.originCoordinate h coordinate)).symm
  rw [hc]
  exact Nat.sub_le_iff_le_add.mpr (by simpa [domain,Nat.add_comm] using W.joined.2.2.1)

end Witness

def chooseWitness {i j : I} (hadj : (graph D color).Adj i j) : Witness D color i j :=
  Classical.choice (exists_witness D color hadj)

def links : Links (T := A) h where
  graph := graph D color
  known i j := if hadj : (graph D color).Adj i j then
    (chooseWitness D color hadj).known h coordinate else ∅
  source i j x := if hadj : (graph D color).Adj i j then
    (chooseWitness D color hadj).source h coordinate ⟨x.val,by simpa only [dif_pos hadj] using x.property⟩
    else False.elim (by simpa only [dif_neg hadj,Finset.notMem_empty] using x.property)
  symbol i j := if hadj : (graph D color).Adj i j then symbol (chooseWitness D color hadj).side
    else Equiv.refl A

theorem links_deficit {i j : I} (hadj : (links D color h coordinate symbol).graph.Adj i j) :
    h i - ((links D color h coordinate symbol).known i j).card ≤ D.error := by
  change (graph D color).Adj i j at hadj
  simpa only [links,dif_pos hadj] using (chooseWitness D color hadj).deficit h coordinate

/-- Any actual comparison-compatible labeling induces full feasible words on
all blocks, including those not present at a chosen multiplicity stage. -/
theorem links_consistent (letters : Ω → A) (words : (i : I) → Fin (h i) → A)
    (hcompare : ∀ x e, D.side x = some e → letters x = symbol e (letters (D.pairing.partner x)))
    (hwords : ∀ b (x : D.positions b), words (color b) (coordinate b x) = letters x.val) :
    (links D color h coordinate symbol).Consistent words := by
  intro i j hadj k
  change (graph D color).Adj i j at hadj
  let W := chooseWitness D color hadj
  let k' : W.known h coordinate := ⟨k.val,by simpa only [links,dif_pos hadj] using k.property⟩
  let x := W.recover h coordinate k'
  have hx := (D.slice_mem.mp x.property).2.1
  have hs := W.recover_spec h coordinate k'
  have word_transport : ∀ b (i : I) (he : color b = i) (y : D.positions b),
      words i ((coordinate b).trans (finCongr (congrArg h he)) y) = letters y.val := by
    intro b i he y
    subst i
    exact hwords b y
  have ho : words i (W.originCoordinate h coordinate (W.includeDomain x)) = letters x.val :=
    word_transport W.origin i W.origin_color (W.includeDomain x)
  have ht : words j (W.targetCoordinate h coordinate (W.compareTarget x)) =
      letters (D.pairing.partner x.val) :=
    word_transport (D.matching.partner W.origin) j W.target_color (W.compareTarget x)
  simp only [links,dif_pos hadj]
  change words i k'.val = symbol W.side (words j (W.source h coordinate k'))
  rw [← hs,ho]
  exact (hcompare x.val W.side hx).trans (congrArg (symbol W.side) ht.symm)

end TorsionFreeZeroDivisors.MatchedLabels

namespace TorsionFreeZeroDivisors.BlockConstraints

open scoped BigOperators

/-- A partial parent map strictly decreasing the position index. -/
structure ParentMap (h : ℕ) where
  parent : Fin h → Option (Fin h)
  decreasing : ∀ j i, parent j = some i → i.val < j.val

namespace ParentMap

variable {h : ℕ} (P : ParentMap h) {T : Type*}

/-- Roots are precisely the positions not constrained to earlier positions. -/
def Root := {j : Fin h // P.parent j = none}

def Consistent (w : Fin h → T) : Prop :=
  ∀ j i, P.parent j = some i → w j = w i

/-- The letters at roots determine every consistent word. -/
theorem determined_by_roots {w v : Fin h → T}
    (hw : P.Consistent w) (hv : P.Consistent v)
    (hr : ∀ r : P.Root, w r.val = v r.val) : w = v := by
  funext j
  have aux : ∀ n : ℕ, ∀ j : Fin h, j.val = n → w j = v j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      cases hp : P.parent j with
      | none => exact hr ⟨j, hp⟩
      | some i =>
        rw [hw j i hp, hv j i hp]
        exact ih i.val (hj ▸ P.decreasing j i hp) i rfl
  exact aux j.val j rfl

/-- A forest of equality constraints costs one free letter per root. -/
theorem card_consistent_le [Fintype T] :
    Nat.card {w : Fin h → T // P.Consistent w} ≤
      (Fintype.card T) ^ Nat.card P.Root := by
  classical
  let : Fintype P.Root := inferInstanceAs (Fintype {j : Fin h // P.parent j = none})
  let restriction : {w : Fin h → T // P.Consistent w} → (P.Root → T) :=
    fun w r => w.val r.val
  have hinj : Function.Injective restriction := by
    intro w v he
    apply Subtype.ext
    exact P.determined_by_roots w.property v.property (congrFun he)
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using
    Fintype.card_le_of_injective restriction hinj

end ParentMap

/-- A set of translated positions; the integral shift is positive. -/
structure Translation (h : ℕ) where
  shift : ℕ
  positive : 0 < shift
  domain : Finset (Fin h)
  bounded : ∀ i ∈ domain, i.val + shift < h

namespace Translation

variable {h : ℕ} (D : Translation h)

/-- The image position of a prescribed comparison. -/
def target (i : D.domain) : Fin h := ⟨i.val.val + D.shift, D.bounded i.val i.property⟩

theorem target_injective : Function.Injective D.target := by
  intro i j he
  have hv := congrArg Fin.val he
  dsimp [target] at hv
  apply Subtype.ext
  apply Fin.ext
  omega

noncomputable def parents : ParentMap h where
  parent j := if hj : ∃ i : D.domain, D.target i = j then some hj.choose.val else none
  decreasing j i hp := by
    classical
    split at hp
    next hex =>
      have hei : hex.choose.val = i := Option.some.inj hp
      have he := congrArg Fin.val hex.choose_spec
      dsimp [target] at he
      have ht := D.positive
      have hlt : hex.choose.val.val < j.val :=
        lt_of_lt_of_eq (Nat.lt_add_of_pos_right ht) he
      simpa only [hei] using hlt
    next => simp at hp

theorem root_iff (j : Fin h) :
    D.parents.parent j = none ↔ j ∉ Set.range D.target := by
  classical
  simp [parents, Set.mem_range]

/-- Each distinct translated edge removes exactly one root. -/
theorem card_roots : Nat.card D.parents.Root = h - D.domain.card := by
  classical
  let e : D.parents.Root ≃ {j : Fin h // j ∉ Set.range D.target} :=
    Equiv.subtypeEquivRight (D.root_iff)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hc : Fintype.card {j : Fin h // j ∈ Set.range D.target} = D.domain.card := by
    change Fintype.card (Set.range D.target) = D.domain.card
    rw [← Fintype.card_coe D.domain]
    exact (Fintype.card_congr (Equiv.ofInjective D.target D.target_injective)).symm
  simpa using congrArg (fun k => h - k) hc

/-- Equalities along a nonzero translation form a forest, even without the
additional contiguous-domain hypothesis in the manuscript. -/
theorem word_count {T : Type*} [Fintype T] :
    Nat.card {w : Fin h → T // ∀ i : D.domain, w (D.target i) = w i.val} ≤
      (Fintype.card T) ^ (h - D.domain.card) := by
  classical
  have heq : (fun w : Fin h → T => ∀ i : D.domain, w (D.target i) = w i.val) =
      D.parents.Consistent := by
    funext w
    apply propext
    constructor
    · intro hw j i hp
      dsimp [parents] at hp
      split at hp
      next hex =>
        have hi := Option.some.inj hp
        exact (congrArg w hex.choose_spec.symm).trans ((hw hex.choose).trans (congrArg w hi))
      next => simp at hp
    · intro hw i
      have hp : D.parents.parent (D.target i) = some i.val := by
        dsimp [parents]
        split
        next hex =>
          congr 1
          exact congrArg Subtype.val (D.target_injective hex.choose_spec)
        next hn => exact False.elim (hn ⟨i, rfl⟩)
      exact hw _ _ hp
  rw [heq]
  simpa [D.card_roots] using D.parents.card_consistent_le (T := T)

end Translation

end TorsionFreeZeroDivisors.BlockConstraints

namespace TorsionFreeZeroDivisors.IntervalSelfLinks
open scoped Classical
open BlockConstraints

/-- The literal increasing coordinate on a contiguous block of integer edge
indices (the manuscript's half-integer centers shifted by 1/2). -/
def coordinate (lo hi : ℤ) : (Finset.Ico lo hi) ≃ Fin (hi-lo).toNat where
  toFun q := ⟨(q.val-lo).toNat,by
    have hq := Finset.mem_Ico.mp q.property
    omega⟩
  invFun k := ⟨lo+k.val,by
    apply Finset.mem_Ico.mpr
    have hk := k.isLt
    omega⟩
  left_inv q := by
    apply Subtype.ext
    have hq := Finset.mem_Ico.mp q.property
    dsimp
    omega
  right_inv k := by
    apply Fin.ext
    dsimp
    omega

theorem coordinate_val {lo hi : ℤ} (q : Finset.Ico lo hi) :
    ((coordinate lo hi q).val : ℤ) = q.val-lo := by
  have hq := Finset.mem_Ico.mp q.property
  dsimp [coordinate]
  omega

variable (lo hi a : ℤ) (D : Finset ℤ)
variable (ha : 0 < a) (hD : ∀ q ∈ D, q ∈ Finset.Ico lo hi ∧ q+a ∈ Finset.Ico lo hi)

def domainEmbedding : D ↪ Fin (hi-lo).toNat where
  toFun q := coordinate lo hi ⟨q.val,(hD q.val q.property).1⟩
  inj' := by
    intro q r he
    have hh := (coordinate lo hi).injective he
    exact Subtype.ext (congrArg (fun z : Finset.Ico lo hi => z.val) hh)

def positiveTranslation : Translation (hi-lo).toNat where
  shift := a.toNat
  positive := by omega
  domain := Finset.univ.map (domainEmbedding lo hi a D hD)
  bounded := by
    intro k hk
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hk
    have hq := Finset.mem_Ico.mp (hD q.val q.property).1
    have ht := Finset.mem_Ico.mp (hD q.val q.property).2
    change (q.val-lo).toNat+a.toNat < (hi-lo).toNat
    omega

theorem positive_card : (positiveTranslation lo hi a D ha hD).domain.card = D.card := by
  simp [positiveTranslation]

theorem positive_consistent {A : Type*} (w : Fin (hi-lo).toNat → A)
    (hcompare : ∀ q (hq : q ∈ D),
      w (coordinate lo hi ⟨q+a,(hD q hq).2⟩) = w (coordinate lo hi ⟨q,(hD q hq).1⟩))
    (k : (positiveTranslation lo hi a D ha hD).domain) :
    w ((positiveTranslation lo hi a D ha hD).target k) = w k.val := by
  obtain ⟨q,_,hk⟩ := Finset.mem_map.mp k.property
  have ht : (positiveTranslation lo hi a D ha hD).target k =
      coordinate lo hi ⟨q.val+a,(hD q.val q.property).2⟩ := by
    apply Fin.ext
    change k.val.val+a.toNat = (q.val+a-lo).toNat
    rw [← hk]
    change (q.val-lo).toNat+a.toNat = (q.val+a-lo).toNat
    have hh := Finset.mem_Ico.mp (hD q.val q.property).1
    omega
  rw [ht,← hk]
  exact hcompare q.val q.property

/-- Either direction of a nonzero translation yields exactly |D| distinct
forest constraints, without requiring a substring to contain the entire block. -/
theorem translation_representation (a : ℤ) (D : Finset ℤ) (ha : a ≠ 0)
    (hD : ∀ q ∈ D, q ∈ Finset.Ico lo hi ∧ q+a ∈ Finset.Ico lo hi) :
    ∃ tr : Translation (hi-lo).toNat, tr.domain.card = D.card ∧
      ∀ (A : Type*) (w : Fin (hi-lo).toNat → A),
        (∀ q (hq : q ∈ D),
          w (coordinate lo hi ⟨q+a,(hD q hq).2⟩) = w (coordinate lo hi ⟨q,(hD q hq).1⟩)) →
          ∀ k : tr.domain, w (tr.target k) = w k.val := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · let add : ℤ ↪ ℤ := ⟨fun q => q+a,fun _ _ hh => add_right_cancel hh⟩
    let D' := D.map add
    have hD' : ∀ q ∈ D', q ∈ Finset.Ico lo hi ∧ q+(-a) ∈ Finset.Ico lo hi := by
      intro q hq
      obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hq
      change r+a ∈ Finset.Ico lo hi ∧ r+a+(-a) ∈ Finset.Ico lo hi
      simpa only [add_neg_cancel_right] using And.intro (hD r hr).2 (hD r hr).1
    refine ⟨positiveTranslation lo hi (-a) D' (by omega) hD',?_,?_⟩
    · rw [positive_card]
      exact Finset.card_map _
    · intro A w hw k
      apply positive_consistent lo hi (-a) D' (by omega) hD' w ?_ k
      intro q hq
      obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hq
      change w (coordinate lo hi ⟨r+a+(-a),_⟩) = w (coordinate lo hi ⟨r+a,_⟩)
      simpa only [add_neg_cancel_right] using (hw r hr).symm
  · exact ⟨positiveTranslation lo hi a D ha hD,positive_card lo hi a D ha hD,
      fun _ w hw => positive_consistent lo hi a D ha hD w hw⟩

/-- Direct reflection obstruction on literal interval coordinates. The reduced
word is the actual block word; no cyclic reduction or external extension is used. -/
theorem reflection_excluded {A : Type*} (bar : A → A)
    (hbar : Function.Involutive bar) (hfree : ∀ x, bar x ≠ x)
    (w : ℤ → A) (L U l u b : ℤ)
    (hl : L ≤ l) (hu : u ≤ U) (_hne : l < u)
    (htl : L ≤ b-(u-1)) (htu : b-l < U)
    (hmass : U-L < 2*(u-l))
    (hred : ∀ q, L ≤ q → q+1 < U → w (q+1) ≠ bar (w q))
    (hcompare : ∀ q, l ≤ q → q < u → w q = bar (w (b-q))) : False := by
  have hleft : 2*l ≤ b := by omega
  have hright : b ≤ 2*(u-1) := by omega
  let i := b/2
  have hrem := Int.emod_nonneg b (by norm_num : (2 : ℤ) ≠ 0)
  have hrem2 := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 2)
  by_cases heven : b%2 = 0
  · have hi : l ≤ i ∧ i < u := by dsimp [i]; omega
    have hb : b-i=i := by dsimp [i]; omega
    have hh := hcompare i hi.1 hi.2
    rw [hb] at hh
    exact hfree (w i) hh.symm
  · have hi : l ≤ i ∧ i+1 < u := by dsimp [i]; omega
    have hb : b-i=i+1 := by dsimp [i]; omega
    have hh := hcompare i hi.1 (by omega)
    rw [hb] at hh
    apply hred i (by omega) (by omega)
    rw [hh,hbar]

end TorsionFreeZeroDivisors.IntervalSelfLinks

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.IntervalSelfLinks
open scoped Classical

/-- Integer positions of one actual comparison within a single block. -/
def selfSlice (L U l u : ℤ) (rev : Bool) (a : ℤ) : Finset ℤ :=
  (Finset.Ico L U ∩ Finset.Ico l u).filter
    (fun q => (if rev then a-1-q else q+a) ∈ Finset.Ico L U)

theorem reflection_slice (L U l u a : ℤ) :
    selfSlice L U l u true a =
      Finset.Ico (max L (max l (a-U))) (min U (min u (a-L))) := by
  ext q
  simp only [selfSlice,Finset.mem_filter,Finset.mem_inter,Finset.mem_Ico,
    ite_true,max_le_iff,lt_min_iff]
  omega

/-- No reversed self-link on a reduced word can cover more than half a block. -/
theorem reflection_not_large {A : Type*} (bar : A → A)
    (hbar : Function.Involutive bar) (hfree : ∀ x, bar x ≠ x)
    (w : ℤ → A) (L U l u a : ℤ)
    (hred : ∀ q, L ≤ q → q+1 < U → w (q+1) ≠ bar (w q))
    (hcompare : ∀ q ∈ selfSlice L U l u true a, w q = bar (w (a-1-q))) :
    2*(selfSlice L U l u true a).card ≤ (Finset.Ico L U).card := by
  by_contra! hn
  rw [reflection_slice,Int.card_Ico,Int.card_Ico] at hn
  let l' := max L (max l (a-U))
  let u' := min U (min u (a-L))
  have hll : L ≤ l' := le_max_left _ _
  have hlb : a-U ≤ l' := (le_max_right _ _).trans (le_max_right _ _)
  have huU : u' ≤ U := min_le_left _ _
  have hub : u' ≤ a-L := (min_le_right _ _).trans (min_le_right _ _)
  have hne : l' < u' := by change _ < 2*(u'-l').toNat at hn; omega
  have hmass : U-L < 2*(u'-l') := by change (U-L).toNat < 2*(u'-l').toNat at hn; omega
  apply reflection_excluded bar hbar hfree w L U l' u' (a-1) hll huU hne
    (by omega) (by omega) hmass hred
  intro q hq hq'
  apply hcompare
  rw [reflection_slice]
  exact Finset.mem_Ico.mpr ⟨hq,hq'⟩

/-- The precise translation constraints retained by a self-link, with its
literal compared-position cardinality and no additional independence premise. -/
theorem translation_from_slice (L U l u a : ℤ) (ha : a ≠ 0) :
    ∃ tr : BlockConstraints.Translation (U-L).toNat,
      tr.domain.card = (selfSlice L U l u false a).card ∧
      ∀ (A : Type*) (w : Fin (U-L).toNat → A),
        (∀ q (hq : q ∈ selfSlice L U l u false a),
          w (coordinate L U ⟨q+a,by simpa [selfSlice] using (Finset.mem_filter.mp hq).2⟩) =
            w (coordinate L U ⟨q,(Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).1⟩)) →
          ∀ k : tr.domain, w (tr.target k) = w k.val := by
  exact translation_representation L U a _ ha (by
    intro q hq
    refine ⟨(Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).1,?_⟩
    simpa [selfSlice] using (Finset.mem_filter.mp hq).2)

/-- The same increasing coordinate, transported along the exact cardinality. -/
def coordinateN (L U : ℤ) (n : ℕ) (hn : n = (U-L).toNat) :
    Finset.Ico L U ≃ Fin n := (coordinate L U).trans (finCongr hn.symm)

theorem coordinateN_val (L U : ℤ) (n : ℕ) (hn : n = (U-L).toNat)
    (q : Finset.Ico L U) : ((coordinateN L U n hn q).val : ℤ) = q.val-L :=
  coordinate_val q

theorem translation_from_slice_at (L U l u a : ℤ) (ha : a ≠ 0)
    (n : ℕ) (hn : n = (U-L).toNat) :
    ∃ tr : BlockConstraints.Translation n,
      tr.domain.card = (selfSlice L U l u false a).card ∧
      ∀ (A : Type*) (w : Fin n → A),
        (∀ q (hq : q ∈ selfSlice L U l u false a),
          w (coordinateN L U n hn ⟨q+a,by simpa [selfSlice] using (Finset.mem_filter.mp hq).2⟩) =
            w (coordinateN L U n hn ⟨q,(Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).1⟩)) →
          ∀ k : tr.domain, w (tr.target k) = w k.val := by
  subst n
  simpa [coordinateN] using translation_from_slice L U l u a ha

end TorsionFreeZeroDivisors.IntervalSelfLinks

/-!
Finite combinatorial and numerical bounds: occurrence pairings,
layer-cake stage counts and selection of one small stage. None of the graph
existence, matching estimates or topological assertions is an assumption here.
-/

namespace TorsionFreeZeroDivisors.EntropyStages

open scoped BigOperators

namespace Pairing

variable {O C : Type*} [Fintype O] [DecidableEq O] [DecidableEq C] (P : Pairing O)

abbrev Unmatched := {o : O // P.partner o = o}

/-- The exact link balance, including isolated blocks and multiple links.
A self-link is excluded only in the component where the bound is used. -/
theorem color_balance (color : O → C) (c : C)
    (hcross : ∀ o, P.partner o ≠ o → color (P.partner o) ≠ color o) :
    2 * Fintype.card {o : O // color o = c} ≤
      Fintype.card O + Fintype.card P.Unmatched := by
  classical
  let f : {o : O // color o = c} →
      {o : O // color o ≠ c} ⊕ P.Unmatched := fun o =>
    if h : P.partner o.val = o.val then .inr ⟨o.val,h⟩
    else .inl ⟨P.partner o.val, by simpa only [o.property] using hcross o.val h⟩
  have hf : Function.Injective f := by
    intro o p he
    dsimp [f] at he
    by_cases ho : P.partner o.val = o.val
    · by_cases hp : P.partner p.val = p.val
      · simp only [dif_pos ho, dif_pos hp] at he
        exact Subtype.ext (congrArg (fun q : P.Unmatched => q.val) (Sum.inr.inj he))
      · simp only [dif_pos ho, dif_neg hp, reduceCtorEq] at he
    · by_cases hp : P.partner p.val = p.val
      · simp only [dif_neg ho, dif_pos hp, reduceCtorEq] at he
      · simp only [dif_neg ho, dif_neg hp] at he
        exact Subtype.ext (P.involutive.injective
          (congrArg (fun q : {o : O // color o ≠ c} => q.val) (Sum.inl.inj he)))
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sum] at hcard
  have htotal : Fintype.card {o : O // color o ≠ c} +
      Fintype.card {o : O // color o = c} = Fintype.card O := by
    rw [Fintype.card_subtype_compl]
    have hle := Fintype.card_subtype_le (fun o : O => color o = c)
    omega
  omega

end Pairing

/-- Exact finite layer-cake identity. Stage j+1 is present precisely when
j is smaller than the occurrence multiplicity. -/
theorem stage_sum (M k : ℕ) (hk : k ≤ M) (a : ℝ) :
    (∑ j ∈ Finset.range M, if j < k then a else 0) = k * a := by
  rw [← Finset.sum_filter]
  have he : (Finset.range M).filter (· < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  simp

/-- A bound for the product of numerical stage estimates selects one stage;
no independence between the random variables at different stages is used. -/
theorem select_stage (M : ℕ) (hM : 0 < M) (logB : Fin M → ℝ) (decay : ℝ)
    (hprod : (∑ j, logB j) ≤ -decay) :
    ∃ j, logB j ≤ -decay / M := by
  by_contra! hn
  have hs : (∑ _j : Fin M, -decay / M) < ∑ j, logB j := by
    exact Finset.sum_lt_sum_of_nonempty ⟨⟨0,hM⟩,Finset.mem_univ _⟩ (fun j _ => hn j)
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have he : (∑ _j : Fin M, -decay / M) = -decay := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [he] at hs
  linarith

/-- Markov/union-bound conclusions can use this exponential version directly. -/
theorem select_exponential_stage (M : ℕ) (hM : 0 < M) (logB : Fin M → ℝ)
    (decay : ℝ) (hprod : (∑ j, logB j) ≤ -decay) :
    ∃ j, Real.exp (logB j) ≤ Real.exp (-decay / M) := by
  obtain ⟨j,hj⟩ := select_stage M hM logB decay hprod
  exact ⟨j,Real.exp_le_exp.mpr hj⟩

end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors
open scoped BigOperators
/-- The cost estimate for a component without a self-link, with the
lower bin bound and unmatched-occurrence correction. -/
theorem component_cost_bound {J : Type*} [Fintype J]
    (m d : J → ℝ) (dmin δ s a₀ z b : ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmin : ∀ i, dmin ≤ d i)
    (hlow : δ * s / 2 ≤ dmin) (hhigh : dmin ≤ a₀ * s)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a₀) (hb : 0 ≤ b)
    (hbalance : 2 * z ≤ (∑ i, m i) + b) :
    -(∑ i, m i * d i) + 2 * z * dmin - δ * s * z ≤
      a₀ * s * b - δ / 2 * s * (∑ i, m i) := by
  have hsum : (∑ i, m i) * dmin ≤ ∑ i, m i * d i := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hmin i) (hm i)
  have hds : 0 ≤ δ * s := mul_nonneg hδ hs
  have hab : 0 ≤ a₀ * s * b := mul_nonneg (mul_nonneg ha hs) hb
  by_cases h : 2 * z ≤ ∑ i, m i
  · have hc : 0 ≤ (∑ i, m i) - 2 * z := sub_nonneg.mpr h
    have hh := mul_le_mul_of_nonneg_left hlow hc
    nlinarith
  · have hc : 0 ≤ 2 * z - ∑ i, m i := by linarith
    have hh := mul_le_mul_of_nonneg_left hhigh hc
    have hz : (2 * z - ∑ i, m i) * (a₀ * s) ≤ b * (a₀ * s) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg ha hs)
      linarith
    have hz' := mul_le_mul_of_nonneg_left hc hds
    nlinarith

/-- A self-link removes the root-word entropy. The remaining cost has the
same decay term, with no unmatched-occurrence correction. -/
theorem selflinked_component_cost_bound {J : Type*} [Fintype J]
    (m d : J → ℝ) (δ s : ℝ) (hm : ∀ i, 0 ≤ m i)
    (hlow : ∀ i, δ * s / 2 ≤ d i) :
    -(∑ i, m i * d i) ≤ -δ / 2 * s * (∑ i, m i) := by
  have hsum : (∑ i, m i) * (δ * s / 2) ≤ ∑ i, m i * d i := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hlow i) (hm i)
  nlinarith

end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.StageFusion

section
open scoped BigOperators
open EntropyStages

/-- Layer-cake identity in the `Fin M` indexing of the selected stages. -/
theorem layers (M k : ℕ) (hk : k ≤ M) (a : ℝ) :
    (∑ j : Fin M, if j.val < k then a else 0) = k*a := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then a else 0)]
  exact stage_sum M k hk a

section Components
variable {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]

def componentCost (self : C → Prop) [DecidablePred self]
    (m : ∀ c, I c → ℕ) (d : ∀ c, I c → ℝ) (z : C → ℕ)
    (dmin : C → ℝ) (δ s : ℝ) (c : C) : ℝ :=
  -(∑ i, (m c i : ℝ)*d c i) + if self c then 0 else (2*dmin c - δ*s) * z c

/-- The component costs added together. Every condition here is the
local bin/link balance, not an assumed probability or conclusion. -/
theorem total_component_cost (self : C → Prop) [DecidablePred self]
    (m : ∀ c, I c → ℕ) (d : ∀ c, I c → ℝ) (z : C → ℕ)
    (dmin b : C → ℝ) (δ s a : ℝ)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : ∀ c, 0 ≤ b c)
    (hlow : ∀ c i, δ*s/2 ≤ d c i)
    (hmin : ∀ c, ¬self c → ∀ i, dmin c ≤ d c i)
    (hminlow : ∀ c, ¬self c → δ*s/2 ≤ dmin c)
    (hminhigh : ∀ c, ¬self c → dmin c ≤ a*s)
    (hbalance : ∀ c, ¬self c → 2*(z c : ℝ) ≤ (∑ i, (m c i : ℝ)) + b c) :
    (∑ c, componentCost self m d z dmin δ s c) ≤
      a*s*(∑ c, b c) - δ/2*s*(∑ c, ∑ i, (m c i : ℝ)) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro c _
  dsimp [componentCost]
  by_cases hc : self c
  · rw [if_pos hc,add_zero]
    have h := selflinked_component_cost_bound (fun i => (m c i : ℝ)) (d c) δ s
      (fun _ => Nat.cast_nonneg _) (hlow c)
    have hh := mul_nonneg (mul_nonneg ha hs) (hb c)
    linarith
  · rw [if_neg hc]
    have h := component_cost_bound (fun i => (m c i : ℝ)) (d c) (dmin c) δ s a (z c) (b c)
      (fun _ => Nat.cast_nonneg _) (hmin c hc) (hminlow c hc) (hminhigh c hc)
      hδ hs ha (hb c) (hbalance c hc)
    nlinarith

end Components

/-- Deterministic final absorption of the unmatched mass and sublinear errors. -/
theorem absorb_errors {δ a H b e : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hb : b ≤ epsilon δ a * H) (he : e ≤ δ*H/8) :
    -δ/2*H + a*b + e ≤ -δ*H/4 := by
  have hd : 0 < 16*(1+a) := by positivity
  have hε : epsilon δ a ≤ δ/(16*(1+a)) := min_le_right _ _
  have hab : a*b ≤ a*(δ/(16*(1+a))*H) := by
    exact mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right hε hH)) ha
  have hratio : a*(δ/(16*(1+a))) ≤ δ/16 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
    have hh : δ/(16*(1+a)) * (16*(1+a)) = δ := div_mul_cancel₀ _ (ne_of_gt hd)
    have hp : 0 ≤ δ/(16*(1+a)) := div_nonneg hδ.le hd.le
    nlinarith
  have hab' := mul_le_mul_of_nonneg_right hratio hH
  nlinarith

end

open scoped Classical BigOperators

section FiniteProbability
variable {Ω P : Type*} [Fintype P] (sample : Finset Ω) (hsample : sample.Nonempty)

/-- Elementary finite Markov bound, including sample restriction. -/
theorem markov_count (Bad : Ω → Prop) [DecidablePred Bad] (X : Ω → ℕ)
    (hX : ∀ ω ∈ sample, Bad ω → 1 ≤ X ω) :
    ((sample.filter Bad).card : ℝ) / sample.card ≤
      ((∑ ω ∈ sample, X ω : ℕ) : ℝ) / sample.card := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (show (sample.filter Bad).card ≤ ∑ ω ∈ sample, X ω from by
    calc
      _ = ∑ ω ∈ sample, if Bad ω then 1 else 0 := by simp
      _ ≤ _ := Finset.sum_le_sum fun ω hω => by
        split_ifs with h
        · exact hX ω hω h
        · exact Nat.zero_le _)

/-- Select a single numerical stage for each pattern. No independence is a
premise, and the chosen stage can depend on the pattern. -/
theorem one_pattern (M : ℕ) (hM : 0 < M) (Bad : Ω → Prop) [DecidablePred Bad]
    (X : Fin M → Ω → ℕ) (logB : Fin M → ℝ) (decay : ℝ)
    (hX : ∀ j ω, ω ∈ sample → Bad ω → 1 ≤ X j ω)
    (hexpect : ∀ j, ((∑ ω ∈ sample, X j ω : ℕ) : ℝ) / sample.card ≤ Real.exp (logB j))
    (hproduct : (∑ j, logB j) ≤ -decay) :
    ((sample.filter Bad).card : ℝ) / sample.card ≤ Real.exp (-decay/M) := by
  obtain ⟨j,hj⟩ := EntropyStages.select_exponential_stage M hM logB decay hproduct
  exact (markov_count sample Bad (X j) (hX j)).trans ((hexpect j).trans hj)

include hsample in
/-- Union bound over the enlarged unlabelled patterns. -/
theorem pattern_union (Bad : P → Ω → Prop) [∀ p, DecidablePred (Bad p)] (B : ℝ)
    (hB : ∀ p, ((sample.filter (Bad p)).card : ℝ) / sample.card ≤ B) :
    ((sample.filter (fun ω => ∃ p, Bad p ω)).card : ℝ) / sample.card ≤
      (Fintype.card P : ℝ)*B := by
  have ho : (0 : ℝ) < sample.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hsample)
  let e : Finset Ω := Finset.univ.biUnion (fun p : P => sample.filter (Bad p))
  have he : sample.filter (fun ω => ∃ p, Bad p ω) = e := by
    ext ω
    simp only [e,Finset.mem_filter,Finset.mem_biUnion,Finset.mem_univ,true_and]
    aesop
  rw [he]
  have hc : e.card ≤ ∑ p, (sample.filter (Bad p)).card := Finset.card_biUnion_le
  have hc' : (e.card : ℝ) ≤ ∑ p, ((sample.filter (Bad p)).card : ℝ) := by
    exact_mod_cast hc
  calc
    _ ≤ (∑ p, ((sample.filter (Bad p)).card : ℝ))/sample.card :=
      div_le_div_of_nonneg_right hc' ho.le
    _ = ∑ p, ((sample.filter (Bad p)).card : ℝ)/sample.card := Finset.sum_div _ _ _
    _ ≤ ∑ _p : P, B := Finset.sum_le_sum (fun p _ => hB p)
    _ = _ := by simp

end FiniteProbability

end TorsionFreeZeroDivisors.StageFusion

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MultiplicityBound
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

end TorsionFreeZeroDivisors.MultiplicityBound

namespace TorsionFreeZeroDivisors.PathMultiplicity
open SimpleGraph WeightedMoore
open PortSubdivision SuppressedMoore
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)
local instance : BEq (V ⊕ D) := instBEqOfDecidableEq

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

lemma reverse_mem_word (d : B) (x : D) (hx : x∈word Γ mark h2 d) :
    Γ.reverse x∈word Γ mark h2 ((suppressed Γ mark h2).reverse d) := by
  obtain ⟨i,rfl⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  let e := (suppressed Γ mark h2).reverse d
  let k := len d
  have hj : k-i.val-1 < len e := by
    rw [chainLength_reverse]
    have hi := i.isLt
    change i.val < k at hi
    omega
  rw [mem_word_iff]
  refine ⟨⟨k-i.val-1,hj⟩,?_⟩
  have hf := endpoint_reverse Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (x:=d) (i:=k-i.val) (by change k-i.val ≤ k; omega)
  have he : k-(k-i.val)=i.val := by omega
  have hs : k-i.val=(k-i.val-1)+1 := by have hi := i.isLt; change i.val < k at hi; omega
  change F^[k-i.val] e.val = τ (F^[k-(k-i.val)] d.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (Γ.reverse (F^[k-i.val-1] e.val))) = τ (τ (F^[i.val] d.val)) at h
  rw [turn_involutive Γ.origin mark h2,turn_involutive Γ.origin mark h2] at h
  have hh := congrArg Γ.reverse h
  rwa [Γ.reverse_reverse] at hh

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.PathMultiplicity
open PortSubdivision
open scoped BigOperators Classical
variable {V D I : Type*} (Γ : PortGraph V D) [Fintype I]

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.IncidenceStages
open scoped Classical BigOperators
open EntropyStages
variable {O D V : Type*} [Fintype O] [Fintype D] [Fintype V]

/-- An incidence remembers its occurrence and which (oriented) half-edge it
uses. Passages pair incidences at a vertex; path endpoints are fixed points. -/
structure Passages (origin : D → V) (port : O → D) extends Pairing O where
  location : ∀ o, origin (port (partner o)) = origin (port o)
  reduced : ∀ o, partner o ≠ o → port (partner o) ≠ port o

namespace Passages
variable {origin : D → V} {port : O → D} (P : Passages origin port)

abbrev AtVertex (v : V) := {o : O // origin (port o) = v}

def localPairing (v : V) : Pairing (AtVertex (origin := origin) (port := port) v) where
  partner o := ⟨P.partner o.val,(P.location o.val).trans o.property⟩
  involutive o := Subtype.ext (P.involutive o.val)

def multiplicity (d : D) : ℕ := Fintype.card {o : O // port o = d}
def maxMultiplicity (v : V) : ℕ :=
  (Finset.univ.filter (fun d => origin d = v)).sup (multiplicity (port := port))

omit [Fintype V] [Fintype D] in
theorem local_multiplicity (d : D) :
    Fintype.card {o : AtVertex (origin := origin) (port := port) (origin d) // port o.val = d} =
      multiplicity (port := port) d := by
  let e : {o : AtVertex (origin := origin) (port := port) (origin d) // port o.val = d} ≃
      {o : O // port o = d} :=
    { toFun := fun o => ⟨o.val.val,o.property⟩
      invFun := fun o => ⟨⟨o.val,congrArg origin o.property⟩,o.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.card_congr e

omit [Fintype V] in
theorem local_balance (v : V) :
    2 * maxMultiplicity (origin := origin) (port := port) v ≤
      Fintype.card (AtVertex (origin := origin) (port := port) v) +
        Fintype.card (P.localPairing v).Unmatched := by
  by_cases hem : (Finset.univ.filter (fun d => origin d = v)).Nonempty
  · obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup _ hem (multiplicity (port := port))
    have hdv : origin d = v := (Finset.mem_filter.mp hd).2
    have hb := (P.localPairing v).color_balance (fun o => port o.val) d (by
      intro o ho
      exact P.reduced o.val (by intro h; exact ho (Subtype.ext h)))
    have hc : Fintype.card {o : AtVertex (origin := origin) (port := port) v // port o.val = d} =
        multiplicity (port := port) d := by
      subst v
      exact local_multiplicity d
    rw [hc] at hb
    simpa only [maxMultiplicity,he] using hb
  · have he : Finset.univ.filter (fun d => origin d = v) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hem
    simp [maxMultiplicity,he]

omit [Fintype D] in
theorem sum_vertex_cards :
    (∑ v : V, Fintype.card (AtVertex (origin := origin) (port := port) v)) = Fintype.card O := by
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    Fintype.sum_fiberwise (fun o => origin (port o)) (fun _ => (1 : ℕ))

omit [Fintype D] in
theorem sum_endpoint_cards :
    (∑ v : V, Fintype.card (P.localPairing v).Unmatched) = Fintype.card P.toPairing.Unmatched := by
  have hc (v : V) : Fintype.card (P.localPairing v).Unmatched =
      Fintype.card {o : P.toPairing.Unmatched // origin (port o.val) = v} := by
    let e : (P.localPairing v).Unmatched ≃
        {o : P.toPairing.Unmatched // origin (port o.val) = v} :=
      { toFun := fun o => ⟨⟨o.val.val,congrArg Subtype.val o.property⟩,o.val.property⟩
        invFun := fun o => ⟨⟨o.val.val,o.property⟩,Subtype.ext o.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  simp_rw [hc]
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    Fintype.sum_fiberwise (fun o : P.toPairing.Unmatched => origin (port o.val)) (fun _ => (1 : ℕ))

/-- Exact incidence balance before any probabilities or asymptotic estimates.
It remains valid when a loop contributes two distinct half-edges at a vertex. -/
theorem total_balance :
    2 * (∑ v : V, maxMultiplicity (origin := origin) (port := port) v) ≤
      Fintype.card O + Fintype.card P.toPairing.Unmatched := by
  calc
    _ = ∑ v : V, 2 * maxMultiplicity (origin := origin) (port := port) v := by rw [Finset.mul_sum]
    _ ≤ ∑ v : V, (Fintype.card (AtVertex (origin := origin) (port := port) v) +
      Fintype.card (P.localPairing v).Unmatched) := Finset.sum_le_sum (fun v _ => P.local_balance v)
    _ = _ := by rw [Finset.sum_add_distrib,sum_vertex_cards,P.sum_endpoint_cards]

/-- Each edge occurrence has two incidences, and zero or one interval
contributes zero or two endpoints. -/
theorem image_vertex_bound (H iota : ℕ) (hH : Fintype.card O = 2*H)
    (hiota : Fintype.card P.toPairing.Unmatched = 2*iota) :
    (∑ v : V, maxMultiplicity (origin := origin) (port := port) v) ≤ H+iota := by
  have h := P.total_balance
  rw [hH,hiota] at h
  omega

end Passages
end TorsionFreeZeroDivisors.IncidenceStages

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PathIncidences

section
open scoped Classical BigOperators
open EntropyStages IncidenceStages

namespace Opened
variable {O : Type*} (P : EntropyStages.Pairing O)

/-- Open one cyclic passage into two interval endpoints. -/
def openAt (c : O) : EntropyStages.Pairing O where
  partner o := if o = c ∨ o = P.partner c then o else P.partner o
  involutive o := by
    by_cases h : o = c ∨ o = P.partner c
    · simp only [if_pos h]
    · have h' : ¬ (P.partner o = c ∨ P.partner o = P.partner c) := by
        rintro (he|he)
        · exact h (Or.inr (by rw [← he,P.involutive]))
        · exact h (Or.inl (P.involutive.injective he))
      simp only [if_neg h,if_neg h']
      exact P.involutive o

theorem openAt_fixed_iff (hfree : ∀ o, P.partner o ≠ o) (c o : O) :
    (openAt P c).partner o = o ↔ o = c ∨ o = P.partner c := by
  dsimp [openAt]
  split_ifs with h
  · simp only [h]
  · exact iff_of_false (hfree o) h

theorem openAt_unmatched_card [Fintype O] [DecidableEq O] (hfree : ∀ o, P.partner o ≠ o) (c : O) :
    Fintype.card (openAt P c).Unmatched = 2 := by
  let e : (openAt P c).Unmatched ≃ Bool :=
    { toFun := fun o => if o.val = c then false else true
      invFun := fun b => if b then
        ⟨P.partner c,by rw [openAt_fixed_iff P hfree]; exact Or.inr rfl⟩ else
        ⟨c,by rw [openAt_fixed_iff P hfree]; exact Or.inl rfl⟩
      left_inv := by
        intro o
        apply Subtype.ext
        obtain h|h := (openAt_fixed_iff P hfree c o.val).mp o.property
        · simp [h]
        · simp [h,hfree c]
      right_inv := by
        intro b
        cases b <;> simp [hfree c] }
  exact (Fintype.card_congr e).trans Fintype.card_bool
end Opened

/-- Cyclic consecutive edge incidences. `succ` is the permutation of edge
positions; opening its passage at one position handles an interval path. -/
def cyclePairing {E : Type*} (succ : Equiv.Perm E) : EntropyStages.Pairing (E × Bool) where
  partner x := if x.2 then (succ x.1,false) else (succ.symm x.1,true)
  involutive x := by
    rcases x with ⟨i,b⟩
    cases b <;> simp

theorem cyclePairing_free {E : Type*} (succ : Equiv.Perm E) (x : E × Bool) :
    (cyclePairing succ).partner x ≠ x := by
  rcases x with ⟨i,b⟩
  cases b <;> simp [cyclePairing]

def pathPairing {E : Type*} (succ : Equiv.Perm E) (cut : Option E) : EntropyStages.Pairing (E × Bool) :=
  match cut with
  | none => cyclePairing succ
  | some c => Opened.openAt (cyclePairing succ) (c,false)

theorem pathPairing_card {E : Type*} [Fintype E] (succ : Equiv.Perm E) (cut : Option E) :
    Fintype.card (pathPairing succ cut).Unmatched = if cut.isSome then 2 else 0 := by
  cases cut with
  | none =>
    have : IsEmpty (pathPairing succ none).Unmatched :=
      ⟨fun o => cyclePairing_free succ o.val o.property⟩
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Fintype.card_of_isEmpty]
  | some c =>
    have h := Opened.openAt_unmatched_card _ (cyclePairing_free succ) (c,false)
    rw [← Nat.card_eq_fintype_card] at h ⊢
    exact h

variable {E D V : Type*} (origin : D → V) (reverse : D → D)
  (edge : E → D)
  (succ : Equiv.Perm E) (cut : Option E)

/-- Initial and terminal half-edge of an occurrence, respectively. -/
def port (x : E × Bool) : D := if x.2 then reverse (edge x.1) else edge x.1

theorem partner_turn {x : E × Bool}
    (hne : (pathPairing succ cut).partner x ≠ x) :
    (pathPairing succ cut).partner x = (cyclePairing succ).partner x ∧
    if x.2 then cut ≠ some (succ x.1) else cut ≠ some x.1 := by
  cases cut with
  | none => simp [pathPairing]
  | some c =>
    have hx : ¬ (x = (c,false) ∨ x = (cyclePairing succ).partner (c,false)) := by
      intro hh
      exact hne (by dsimp [pathPairing,Opened.openAt]; rw [if_pos hh])
    refine ⟨by dsimp [pathPairing,Opened.openAt]; rw [if_neg hx],?_⟩
    rcases x with ⟨i,b⟩
    cases b
    · simp only [Bool.false_eq_true,↓reduceIte,ne_eq,Option.some.injEq]
      intro he
      exact hx (Or.inl (Prod.ext he.symm rfl))
    · simp only [↓reduceIte,ne_eq,Option.some.injEq]
      intro he
      exact hx (Or.inr (by
        simp only [cyclePairing,Bool.false_eq_true,↓reduceIte]
        exact Prod.ext (by rw [he,Equiv.symm_apply_apply]) rfl))

/-- The incidence passage data is derived from the actual adjacency and
nonbacktracking conditions, not assumed as an extra vertex-count estimate. -/
def passages
    (hvertex : ∀ i, cut ≠ some (succ i) → origin (edge (succ i)) = origin (reverse (edge i)))
    (hreduced : ∀ i, cut ≠ some (succ i) → edge (succ i) ≠ reverse (edge i)) :
    IncidenceStages.Passages origin (port reverse edge) where
  toPairing := pathPairing succ cut
  location x := by
    by_cases he : (pathPairing succ cut).partner x = x
    · rw [he]
    obtain ⟨hp,hc⟩ := partner_turn succ cut he
    rw [hp]
    rcases x with ⟨i,b⟩
    cases b
    · have ht := hvertex (succ.symm i) (by simpa using hc)
      simpa [cyclePairing,port] using ht.symm
    · simpa [cyclePairing,port] using hvertex i hc
  reduced x he := by
    obtain ⟨hp,hc⟩ := partner_turn succ cut he
    rw [hp]
    rcases x with ⟨i,b⟩
    cases b
    · have ht := hreduced (succ.symm i) (by simpa using hc)
      simpa [cyclePairing,port] using ht.symm
    · simpa [cyclePairing,port] using hreduced i hc

end

open scoped Classical BigOperators
open EntropyStages IncidenceStages

theorem card_toNat {A : Type*} (inst : Fintype A) : @Fintype.card A inst = Nat.card A :=
  (@Nat.card_eq_fintype_card A inst).symm

/-- Disjoint union of the passages of the individual path components. -/
def familyPairing {I : Type*} {O : I → Type*} (P : ∀ i, EntropyStages.Pairing (O i)) :
    EntropyStages.Pairing (Sigma O) where
  partner x := ⟨x.1,(P x.1).partner x.2⟩
  involutive x := by
    rcases x with ⟨i,o⟩
    exact congrArg (Sigma.mk i) ((P i).involutive o)

def unmatchedEquiv {I : Type*} {O : I → Type*} (P : ∀ i, EntropyStages.Pairing (O i)) :
    (familyPairing P).Unmatched ≃ (Σ i, (P i).Unmatched) where
  toFun x := ⟨x.val.1,⟨x.val.2,by
    have h := x.property
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩⟩
  invFun x := ⟨⟨x.1,x.2.val⟩,congrArg (Sigma.mk x.1) x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem family_unmatched_card {I : Type*} [Fintype I] {O : I → Type*}
    [∀ i, Fintype (O i)] (P : ∀ i, EntropyStages.Pairing (O i)) :
    Fintype.card (familyPairing P).Unmatched = ∑ i, Fintype.card (P i).Unmatched := by
  rw [Fintype.card_congr (unmatchedEquiv P), Fintype.card_sigma]

variable {I D V : Type*} [Fintype I] [Fintype D] [Fintype V] {E : I → Type*}
  [∀ i, Fintype (E i)] (origin : D → V) (reverse : D → D)
  (edge : ∀ i, E i → D) (succ : ∀ i, Equiv.Perm (E i)) (cut : ∀ i, Option (E i))
  (hvertex : ∀ i e, cut i ≠ some (succ i e) →
    origin (edge i (succ i e)) = origin (reverse (edge i e)))
  (hreduced : ∀ i e, cut i ≠ some (succ i e) →
    edge i (succ i e) ≠ reverse (edge i e))

def familyPort (x : Σ i, E i × Bool) : D := port reverse (edge x.1) x.2

def familyPassages : IncidenceStages.Passages origin (familyPort reverse edge) where
  toPairing := familyPairing (fun i => pathPairing (succ i) (cut i))
  location x := (passages origin reverse (edge x.1) (succ x.1) (cut x.1)
    (hvertex x.1) (hreduced x.1)).location x.2
  reduced x he := (passages origin reverse (edge x.1) (succ x.1) (cut x.1)
    (hvertex x.1) (hreduced x.1)).reduced x.2 (fun h => he (congrArg (Sigma.mk x.1) h))

include succ hvertex hreduced in
/-- The exact occurrence balance for any union of immersed circles and
intervals. -/
theorem family_vertex_bound :
    (∑ v : V, IncidenceStages.Passages.maxMultiplicity
      (origin := origin) (port := familyPort reverse edge) v) ≤
      (∑ i, Fintype.card (E i)) + ∑ i, if (cut i).isSome then 1 else 0 := by
  apply (familyPassages origin reverse edge succ cut hvertex hreduced).image_vertex_bound
  · simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_bool,
      ← Finset.sum_mul,mul_comm]
  · have h := family_unmatched_card (fun i => pathPairing (succ i) (cut i))
    rw [card_toNat] at h ⊢
    change Nat.card (familyPairing (fun i => pathPairing (succ i) (cut i))).Unmatched = _
    rw [h]
    have hp (i : I) : Fintype.card (pathPairing (succ i) (cut i)).Unmatched =
        if (cut i).isSome then 2 else 0 := pathPairing_card (succ i) (cut i)
    simp_rw [card_toNat] at hp ⊢
    simp_rw [hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num

end TorsionFreeZeroDivisors.PathIncidences

namespace TorsionFreeZeroDivisors.StageSubgraphs
open scoped Classical BigOperators
open PortSubdivision
variable {V D : Type*} [Fintype V] [Fintype D] (Γ : PortGraph V D)

abbrev ActiveD (m : D → ℕ) (j : ℕ) := {d : D // j < m d}
abbrev ActiveV (m : D → ℕ) (j : ℕ) := {v : V // ∃ d, Γ.origin d = v ∧ j < m d}

/-- The actual multiplicity stage has precisely its incident vertices.
No inactive vertices are counted or forced to embed. -/
def stage (m : D → ℕ) (hm : ∀ d, m (Γ.reverse d) = m d) (j : ℕ) :
    PortGraph (ActiveV Γ m j) (ActiveD m j) where
  origin d := ⟨Γ.origin d.val, d.val,rfl,d.property⟩
  reverse d := ⟨Γ.reverse d.val, (hm d.val).symm ▸ d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d.val)
  reverse_ne d he := Γ.reverse_ne d.val (congrArg Subtype.val he)

def maxAt (m : D → ℕ) (v : V) : ℕ :=
  (Finset.univ.filter fun d => Γ.origin d = v).sup m

omit [Fintype V] in
theorem active_iff (m : D → ℕ) (j : ℕ) (v : V) :
    (∃ d, Γ.origin d = v ∧ j < m d) ↔ j < maxAt Γ m v := by
  simp [maxAt,Finset.lt_sup_iff]

theorem vertex_card (m : D → ℕ) (j : ℕ) :
    Fintype.card (ActiveV Γ m j) = ∑ v : V, if j < maxAt Γ m v then 1 else 0 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (active_iff Γ m j))]
  simp only [Fintype.card_subtype,Finset.card_filter]

theorem sum_vertex_card (m : D → ℕ) (M : ℕ) (hm : ∀ d, m d ≤ M) :
    (∑ j : Fin M, Fintype.card (ActiveV Γ m j.val)) = ∑ v : V, maxAt Γ m v := by
  simp_rw [vertex_card]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  have hv : maxAt Γ m v ≤ M := Finset.sup_le (fun d _ => hm d)
  rw [← Finset.card_filter]
  have he : (Finset.univ.filter fun j : Fin M => j.val < maxAt Γ m v) =
      Finset.univ.filter fun j => j.val ∈ Finset.range (maxAt Γ m v) := by simp
  rw [he]
  rw [← Fintype.card_subtype]
  let e : {j : Fin M // j.val ∈ Finset.range (maxAt Γ m v)} ≃ Fin (maxAt Γ m v) :=
    { toFun := fun j => ⟨j.val.val,Finset.mem_range.mp j.property⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt hv⟩,Finset.mem_range.mpr j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- Literal undirected stage edges; both orientations name a single edge. -/
def edges : Finset (Sym2 D) := Finset.univ.image (fun d => s(d,Γ.reverse d))
def edgeName (d : D) : edges Γ := ⟨s(d,Γ.reverse d),Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩⟩

omit [Fintype V] in
theorem fiber_card (e : edges Γ) : Fintype.card {d : D // edgeName Γ d = e} = 2 := by
  obtain ⟨d,_,hd⟩ := Finset.mem_image.mp e.property
  have he : e = edgeName Γ d := Subtype.ext hd.symm
  subst e
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter fun x => edgeName Γ x = edgeName Γ d) = {d,Γ.reverse d} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [Subtype.ext_iff]
    change s(x,Γ.reverse x) = s(d,Γ.reverse d) ↔ x = d ∨ x = Γ.reverse d
    rw [Sym2.eq_iff]
    constructor
    · rintro (⟨h,_⟩|⟨h,_⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl|rfl)
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,Γ.reverse_reverse d⟩
  rw [hf,Finset.card_pair (Ne.symm (Γ.reverse_ne d))]

omit [Fintype V] in
/-- A fixed-point-free port involution has exactly two darts per edge. -/
theorem two_edges : 2*(edges Γ).card = Fintype.card D := by
  have h := Fintype.card_sigma (α := fun e : edges Γ => {d : D // edgeName Γ d = e})
  simp_rw [fiber_card] at h
  have he : (Σ e : edges Γ, {d : D // edgeName Γ d = e}) ≃ D :=
    Equiv.sigmaFiberEquiv (edgeName Γ)
  rw [Fintype.card_congr he] at h
  simpa [mul_comm] using h.symm

omit [Fintype V] in
theorem sum_dart_card (m : D → ℕ) (M : ℕ) (hm : ∀ d, m d ≤ M) :
    (∑ j : Fin M, Fintype.card (ActiveD m j.val)) = ∑ d : D, m d := by
  simp only [ActiveD,Fintype.card_subtype,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.card_filter,← Fintype.card_subtype]
  let e : {j : Fin M // j.val < m d} ≃ Fin (m d) :=
    { toFun := fun j => ⟨j.val.val,j.property⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt (hm d)⟩,j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

omit [Fintype V] in
/-- Counting actual stage edges with multiplicity, not expected edges. -/
theorem sum_edge_card (m : D → ℕ) (hr : ∀ d, m (Γ.reverse d) = m d)
    (M H : ℕ) (hm : ∀ d, m d ≤ M) (hH : ∑ d, m d = 2*H) :
    (∑ j : Fin M, (edges (stage Γ m hr j.val)).card) = H := by
  have h2 : 2*(∑ j : Fin M, (edges (stage Γ m hr j.val)).card) = 2*H := by
    rw [Finset.mul_sum]
    simp_rw [two_edges]
    rw [sum_dart_card m M hm,hH]
  omega

variable {I : Type*} [Fintype I] {E : I → Type*} [∀ i, Fintype (E i)]
  (edge : ∀ i, E i → D)

def multiplicity (d : D) : ℕ := IncidenceStages.Passages.multiplicity
  (port := PathIncidences.familyPort Γ.reverse edge) d

omit [Fintype V] [Fintype D] in
/-- Source traversal multiplicity agrees on the two orientations. -/
theorem multiplicity_reverse (d : D) :
    multiplicity Γ edge (Γ.reverse d) = multiplicity Γ edge d := by
  let flip : (Σ i, E i × Bool) ≃ (Σ i, E i × Bool) :=
    { toFun := fun x => ⟨x.1,x.2.1,!x.2.2⟩
      invFun := fun x => ⟨x.1,x.2.1,!x.2.2⟩
      left_inv := by rintro ⟨i,e,b⟩; cases b <;> rfl
      right_inv := by rintro ⟨i,e,b⟩; cases b <;> rfl }
  have hf (x : Σ i, E i × Bool) :
      PathIncidences.familyPort Γ.reverse edge (flip x) =
        Γ.reverse (PathIncidences.familyPort Γ.reverse edge x) := by
    rcases x with ⟨i,e,b⟩
    cases b
    · rfl
    · exact (Γ.reverse_reverse (edge i e)).symm
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv flip (fun o => by
    rw [hf]
    constructor
    · intro h
      rw [h,Γ.reverse_reverse]
    · intro h
      exact Γ.reverse_reverse.injective ((Γ.reverse_reverse d).symm ▸ h))

omit [Fintype V] in
/-- Each edge occurrence contributes one incidence in each orientation. -/
theorem sum_multiplicity : (∑ d : D, multiplicity Γ edge d) =
    2*(∑ i, Fintype.card (E i)) := by
  have h := Fintype.card_sigma (α := fun d : D =>
    {o : Σ i, E i × Bool // PathIncidences.familyPort Γ.reverse edge o = d})
  have e := Equiv.sigmaFiberEquiv (PathIncidences.familyPort Γ.reverse edge)
  rw [Fintype.card_congr e] at h
  simpa only [multiplicity,IncidenceStages.Passages.multiplicity,Fintype.card_sigma,
    Fintype.card_prod,Fintype.card_bool,← Finset.sum_mul,mul_comm] using h.symm

variable (succ : ∀ i, Equiv.Perm (E i)) (cut : ∀ i, Option (E i))
  (hvertex : ∀ i e, cut i ≠ some (succ i e) →
    Γ.origin (edge i (succ i e)) = Γ.origin (Γ.reverse (edge i e)))
  (hreduced : ∀ i e, cut i ≠ some (succ i e) →
    edge i (succ i e) ≠ Γ.reverse (edge i e))

include succ hvertex hreduced in
/-- Exact vertex inequality for the actual stages
of the immersed family, derived from the literal consecutive passages. -/
theorem family_vertex_total (M : ℕ) (hm : ∀ d, multiplicity Γ edge d ≤ M) :
    (∑ j : Fin M, Fintype.card (ActiveV Γ (multiplicity Γ edge) j.val)) ≤
      (∑ i, Fintype.card (E i)) + ∑ i, if (cut i).isSome then 1 else 0 := by
  rw [sum_vertex_card Γ _ M hm]
  exact PathIncidences.family_vertex_bound Γ.origin Γ.reverse edge succ cut hvertex hreduced

omit [Fintype V] in
/-- Every traversal contributes exactly one undirected edge over all stages. -/
theorem family_edge_total (M : ℕ) (hm : ∀ d, multiplicity Γ edge d ≤ M) :
    (∑ j : Fin M, (edges (stage Γ (multiplicity Γ edge)
      (multiplicity_reverse Γ edge) j.val)).card) = ∑ i, Fintype.card (E i) :=
  sum_edge_card Γ _ (multiplicity_reverse Γ edge) M _ hm (sum_multiplicity Γ edge)

include succ hvertex hreduced in
/-- The n-exponent of actual stage embeddings is nonpositive; the initial
vertex saving is claimed only at the first stage of every rooted interval. -/
theorem family_exponent_nonpos (M : ℕ) (hM : 0 < M)
    (hm : ∀ d, multiplicity Γ edge d ≤ M) :
    (∑ j : Fin M, ((Fintype.card (ActiveV Γ (multiplicity Γ edge) j.val) : ℤ) -
      (edges (stage Γ (multiplicity Γ edge) (multiplicity_reverse Γ edge) j.val)).card -
      if j.val = 0 then (∑ i, if (cut i).isSome then 1 else 0 : ℕ) else 0)) ≤ 0 := by
  have hv := family_vertex_total Γ edge succ cut hvertex hreduced M hm
  have he := family_edge_total Γ edge M hm
  have hp : (∑ j : Fin M, if j.val = 0 then
      ((∑ i, if (cut i).isSome then 1 else 0 : ℕ) : ℤ) else 0) =
      ((∑ i, if (cut i).isSome then 1 else 0 : ℕ) : ℤ) := by
    rw [Finset.sum_eq_single (⟨0,hM⟩ : Fin M)]
    · simp
    · intro b _ hb
      have hb0 : b.val ≠ 0 := fun h => hb (Fin.ext h)
      simp [hb0]
    · simp
  simp only [Finset.sum_sub_distrib, Nat.cast_ite, Nat.cast_zero]
  rw [hp,← Nat.cast_sum,← Nat.cast_sum,he]
  have hv' : ((∑ j : Fin M, Fintype.card (ActiveV Γ (multiplicity Γ edge) j.val)) : ℤ) ≤
      ((∑ i, Fintype.card (E i)) : ℤ) +
      ((∑ i, if (cut i).isSome then 1 else 0 : ℕ) : ℤ) := by exact_mod_cast hv
  omega

end TorsionFreeZeroDivisors.StageSubgraphs

end

end OAI
end

section
namespace OAI



section

/-!
The uniform maximum-degree exclusion bound for finite graph balls.
This treats labelled port graphs too: `neighbors` forgets multiplicities;
loops and multiple edges only decrease the number of distinct vertices.
-/

namespace TorsionFreeZeroDivisors.BallCount

open scoped BigOperators
noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Endpoints of walks of exactly k steps. -/
def ends (neighbors : V → Finset V) (x : V) : ℕ → Finset V
  | 0 => {x}
  | k + 1 => (ends neighbors x k).biUnion neighbors

/-- Finite closed combinatorial ball. -/
def ball (neighbors : V → Finset V) (x : V) (r : ℕ) : Finset V :=
  (Finset.range (r + 1)).biUnion (ends neighbors x)

theorem card_ends_le (neighbors : V → Finset V) (d : ℕ)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (k : ℕ) :
    (ends neighbors x k).card ≤ d ^ k := by
  induction k with
  | zero => simp [ends]
  | succ k ih =>
    calc
      (ends neighbors x (k+1)).card ≤
          ∑ v ∈ ends neighbors x k, (neighbors v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ ends neighbors x k, d := Finset.sum_le_sum fun v _ => hd v
      _ = (ends neighbors x k).card * d := by simp
      _ ≤ d^k * d := Nat.mul_le_mul_right d ih
      _ = d^(k+1) := (pow_succ d k).symm

/-- A non-asymptotic geometric-sum bound. -/
theorem sum_powers_le (d r : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range (r+1), d^k ≤ 2 * d^r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 < d^r := pow_pos (by omega) _
    have hm : 2 * d^r ≤ d^r*d := by nlinarith
    omega

theorem card_ball_le (neighbors : V → Finset V) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (r : ℕ) :
    (ball neighbors x r).card ≤ d^(r+1) := by
  calc
    (ball neighbors x r).card ≤ ∑ k ∈ Finset.range (r+1), (ends neighbors x k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (r+1), d^k :=
      Finset.sum_le_sum fun k _ => card_ends_le neighbors d hd x k
    _ ≤ 2 * d^r - 1 := sum_powers_le d r h2
    _ ≤ d^(r+1) := by
      rw [pow_succ]
      have hm : 2*d^r ≤ d^r*d := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d^r) h2
      omega

@[simp] theorem mem_ball_iff (neighbors : V → Finset V) (x y : V) (r : ℕ) :
    y ∈ ball neighbors x r ↔ ∃ k ≤ r, y ∈ ends neighbors x k := by
  simp [ball]

/-- The ordinary finite neighbor set, with its classical finiteness data fixed. -/
def graphNeighbors [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact G.neighborFinset v

omit [DecidableEq V] in
@[simp] theorem mem_graphNeighbors [Fintype V] (G : SimpleGraph V) (a b : V) :
    b ∈ graphNeighbors G a ↔ G.Adj a b := by
  classical
  simp [graphNeighbors]

omit [DecidableEq V] in
theorem card_graphNeighbors [Fintype V] (G : SimpleGraph V) (v : V) :
    (graphNeighbors G v).card = Nat.card (G.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  exact SimpleGraph.card_neighborFinset_eq_degree G v

/-- The finite combinatorial balls contain all walk endpoints, not just paths. -/
theorem mem_ends_of_walk [Fintype V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b) :
    b ∈ ends (graphNeighbors G) a p.length := by
  classical
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => simp [ends]
  | @Hconcat a b c p h ih =>
    simp only [SimpleGraph.Walk.length_concat,ends,Finset.mem_biUnion]
    exact ⟨b,ih,by simpa using h⟩

theorem mem_ball_of_walk [Fintype V] (G : SimpleGraph V) {a b : V}
    (p : G.Walk a b) (r : ℕ) (hr : p.length ≤ r) : b ∈ ball (graphNeighbors G) a r := by
  exact mem_ball_iff _ _ _ _ |>.mpr ⟨p.length,hr,mem_ends_of_walk G p⟩

theorem far_of_not_mem_ball [Fintype V] (G : SimpleGraph V) {a b : V} (r : ℕ)
    (h : b ∉ ball (graphNeighbors G) a r) (p : G.Walk a b) : r < p.length := by
  by_contra hn
  exact h (mem_ball_of_walk G p r (by omega))

section Matchings
variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Removing source and target ports in a bad vertex set discards at most twice
its cardinality, since each labelled carrier embeds in the vertex set. -/
theorem matching_bad_card (f : X ≃ Y) (locX : X → V) (locY : Y → V)
    (hX : Function.Injective locX) (hY : Function.Injective locY) (B : Finset V) :
    (Finset.univ.filter (fun u => locX u ∈ B ∨ locY (f u) ∈ B)).card ≤ 2 * B.card := by
  classical
  have hx : (Finset.univ.filter (fun u => locX u ∈ B)).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn locX
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · exact hX.injOn
  have hy : (Finset.univ.filter (fun u => locY (f u) ∈ B)).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun u => locY (f u))
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · exact (hY.comp f.injective).injOn
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- A labelled matching has uniformly many choices outside both endpoint balls
and outside a prescribed set. This is the quantitative geometric input to the
conditioned transposition injection. -/
theorem admissible_card (f : X ≃ Y) (locX : X → V) (locY : Y → V)
    (hX : Function.Injective locX) (hY : Function.Injective locY)
    (neighbors : V → Finset V) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, (neighbors v).card ≤ d) (x y : V) (r : ℕ) (P : Finset X) :
    Fintype.card X - P.card - 4*d^(r+1) ≤
      (Finset.univ.filter (fun u => u ∉ P ∧
        locX u ∉ ball neighbors x r ∪ ball neighbors y r ∧
        locY (f u) ∉ ball neighbors x r ∪ ball neighbors y r)).card := by
  classical
  let B := ball neighbors x r ∪ ball neighbors y r
  let bad := Finset.univ.filter (fun u => locX u ∈ B ∨ locY (f u) ∈ B)
  have hb : bad.card ≤ 4*d^(r+1) := by
    have hb' := matching_bad_card f locX locY hX hY B
    have hB : B.card ≤ 2*d^(r+1) :=
      (Finset.card_union_le _ _).trans (by
        have hx := card_ball_le neighbors d h2 hd x r
        have hy := card_ball_le neighbors d h2 hd y r
        omega)
    exact hb'.trans (by omega)
  have he : Finset.univ.filter (fun u => u ∉ P ∧ locX u ∉ B ∧ locY (f u) ∉ B) =
      Finset.univ \ (P ∪ bad) := by
    ext u
    simp [bad, not_or]
  change _ ≤ (Finset.univ.filter (fun u => u ∉ P ∧ locX u ∉ B ∧ locY (f u) ∉ B)).card
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
  have hu := Finset.card_union_le P bad
  omega

end Matchings
end
end TorsionFreeZeroDivisors.BallCount


/-!
A faithful simple-graph encoding of the manuscript's labelled multigraphs.
An original edge has two opposite ports, and its threefold subdivision is
original vertex -- port -- opposite port -- original vertex. Loops become
triangles and parallel edges remain distinct, so neither is silently discarded.
-/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- All degrees are controlled by the fixed port fibers. -/
theorem subdivision_degree (Γ : PortGraph V D) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d) (a : V ⊕ D) :
    (graphNeighbors Γ.subdivision a).card ≤ d := by
  classical
  rw [card_graphNeighbors]
  cases a with
  | inl v => rw [Γ.card_original_neighbors]; exact hd v
  | inr e => rw [Γ.card_port_neighbors]; exact h2

/-- Uniformly many ports of one label lie outside both endpoint neighborhoods. -/
theorem exists_far_port (Γ : PortGraph V D) (label : D → T)
    (d R : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d)
    (x : D) (hbig : 4*d^(R+1) < Nat.card {e : D // label e = label x}) :
    ∃ e : D, label e = label x ∧
      ∀ a ∈ ({Sum.inr x,Sum.inr (Γ.reverse x)} : Set (V ⊕ D)),
      ∀ b ∈ ({Sum.inr e,Sum.inr (Γ.reverse e)} : Set (V ⊕ D)),
      ∀ p : Γ.subdivision.Walk a b, R < p.length := by
  classical
  let X := {e : D // label e = label x}
  let locX : X → V ⊕ D := fun e => .inr e.val
  let locY : X → V ⊕ D := fun e => .inr (Γ.reverse e.val)
  have hX : Function.Injective locX := by
    intro a b h; exact Subtype.ext (Sum.inr.inj h)
  have hY : Function.Injective locY := by
    intro a b h
    exact Subtype.ext (Γ.reverse_reverse.injective (Sum.inr.inj h))
  let B := ball (graphNeighbors Γ.subdivision) (Sum.inr x) R ∪
    ball (graphNeighbors Γ.subdivision) (Sum.inr (Γ.reverse x)) R
  have hB : B.card ≤ 2*d^(R+1) := by
    have ha := card_ball_le (graphNeighbors Γ.subdivision) d h2
      (subdivision_degree Γ d h2 hd) (Sum.inr x) R
    have hb := card_ball_le (graphNeighbors Γ.subdivision) d h2
      (subdivision_degree Γ d h2 hd) (Sum.inr (Γ.reverse x)) R
    exact (Finset.card_union_le _ _).trans (by omega)
  have hbad := matching_bad_card (Equiv.refl X) locX locY hX hY B
  have hlt : (Finset.univ.filter (fun e : X => locX e ∈ B ∨ locY e ∈ B)).card <
      Fintype.card X := by
    rw [Nat.card_eq_fintype_card] at hbig
    change _ < Fintype.card X at hbig
    exact lt_of_le_of_lt (hbad.trans (by omega)) hbig
  obtain ⟨e,he,hebad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Finset.univ.filter (fun e : X => locX e ∈ B ∨ locY e ∈ B))
    (t := (Finset.univ : Finset X)) (by simpa only [Finset.card_univ] using hlt)
  have he' : locX e ∉ B ∧ locY e ∉ B := by simpa only [Finset.mem_filter,
    Finset.mem_univ,true_and,not_or] using hebad
  refine ⟨e.val,e.property,?_⟩
  intro a ha b hb p
  have hn : b ∉ ball (graphNeighbors Γ.subdivision) a R := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun h => he'.1 (Finset.mem_union_left _ h)
    · exact fun h => he'.2 (Finset.mem_union_left _ h)
    · exact fun h => he'.1 (Finset.mem_union_right _ h)
    · exact fun h => he'.2 (Finset.mem_union_right _ h)
  exact far_of_not_mem_ball Γ.subdivision R hn p

omit [Fintype V] [Fintype D] in
/-- The conjugation switch is exactly the graph two-switch used in girth repair. -/
theorem subdivision_switch (Γ : PortGraph V D) (x e : D)
    (hxe : x ≠ e) (hxr : x ≠ Γ.reverse e) :
    (Γ.switch x e).subdivision =
      addEdge (addEdge (Γ.subdivision.deleteEdges
        {s(Sum.inr x,Sum.inr (Γ.reverse x)),s(Sum.inr e,Sum.inr (Γ.reverse e))})
        (Sum.inr x) (Sum.inr (Γ.reverse e))) (Sum.inr e) (Sum.inr (Γ.reverse x)) := by
  ext a b
  rw [Γ.switch_adj x e hxe hxr]
  simp only [addEdge_adj,SimpleGraph.deleteEdges_adj,Set.mem_insert_iff,
    Set.mem_singleton_iff,not_or]
  have her : e ≠ Γ.reverse x := by
    intro h
    apply hxr
    rw [h,Γ.reverse_reverse]
  have h1 : s(a,b) = s(Sum.inr x,Sum.inr (Γ.reverse e)) → a ≠ b := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using hxr
    · simpa using Ne.symm hxr
  have h2 : s(a,b) = s(Sum.inr e,Sum.inr (Γ.reverse x)) → a ≠ b := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using her
    · simpa using Ne.symm her
  tauto

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.ConditionedMatchings
open PortSubdivision BallCount GirthSwitch MatchingGraphs
variable {V D T : Type*}

namespace Matching
variable {label : D → T} {bar : T → T}
instance : CoeFun (Matching label bar) (fun _ => D → D) := ⟨fun r => r.val⟩
instance : DecidableEq (Matching label bar) := Classical.decEq _

theorem label_reverse (r : Matching label bar) (x : D) :
    label (r x) = bar (label x) := r.property.2.2 x

@[ext] theorem ext {r s : Matching label bar} (h : ∀ x, r x = s x) : r = s :=
  Subtype.ext (Equiv.ext h)

variable [DecidableEq D]

/-- Conjugating by the transposition of equally labelled ports. -/
def switch (r : Matching label bar) (x e : D) (he : label x = label e) : Matching label bar :=
  ⟨(Equiv.swap x e).trans (r.val.trans (Equiv.swap x e)),by
    constructor
    · intro f; simp
    constructor
    · intro f h
      have h' := congrArg (Equiv.swap x e) h
      simp only [Equiv.trans_apply,Equiv.swap_apply_self] at h'
      exact r.property.2.1 ((Equiv.swap x e) f) h'
    · intro f
      change label ((Equiv.swap x e) (r ((Equiv.swap x e) f))) = bar (label f)
      rw [PortGraph.label_swap label x e he, r.label_reverse,PortGraph.label_swap label x e he]⟩

@[simp] theorem switch_apply (r : Matching label bar) (x e : D) (he : label x = label e) (f : D) :
    r.switch x e he f = (Equiv.swap x e) (r ((Equiv.swap x e) f)) := rfl

@[simp] theorem switch_switch (r : Matching label bar) (x e : D) (he : label x = label e) :
    (r.switch x e he).switch x e he = r := by
  ext f
  simp

theorem graph_switch (r : Matching label bar) (origin : D → V)
    (x e : D) (he : label x = label e) :
    (r.switch x e he).graph origin = (r.graph origin).switch x e := rfl

/-- Given the new matching and the fixed old pair x,y, the auxiliary port
is forced. This is the reconstructibility behind the conditional estimate. -/
theorem switch_recover (r : Matching label bar) (x y e : D)
    (he : label x = label e) (hxy : r x = y)
    (hbar : ∀ t, bar t ≠ t) : r.switch x e he y = e := by
  have hyx : y ≠ x := hxy ▸ r.property.2.1 x
  have hye : y ≠ e := by
    intro h
    have hl := r.label_reverse x
    rw [hxy,h,← he] at hl
    exact hbar (label x) hl.symm
  simp only [switch_apply,Equiv.swap_apply_of_ne_of_ne hyx hye]
  rw [← hxy,r.reverse_reverse,Equiv.swap_apply_left]

/-- Distinct input-matching/auxiliary-port pairs always give distinct outputs. -/
theorem switch_injective (x y : D) (hbar : ∀ t, bar t ≠ t) :
    Function.Injective (fun p : {r : Matching label bar // r x = y} ×
      {e : D // label x = label e} => p.1.val.switch x p.2.val p.2.property) := by
  rintro ⟨⟨r,hr⟩,⟨e,he⟩⟩ ⟨⟨s,hs⟩,⟨f,hf⟩⟩ h
  have hef : e = f := by
    simpa only [switch_recover r x y e he hr hbar,switch_recover s x y f hf hs hbar]
      using congrArg (fun r : Matching label bar => r y) h
  subst f
  have hrs : r = s := by
    simpa only [switch_switch] using congrArg (fun r : Matching label bar => r.switch x e he) h
  subst s
  rfl

omit [DecidableEq D] in
/-- A signed label chooses a unique orientation of each matching edge. -/
theorem edge_name_injective (r : Matching label bar) (x : D)
    (hbar : ∀ t, bar t ≠ t) :
    Function.Injective (fun e : {e : D // label e = label x} => s(e.val,r e.val)) := by
  rintro ⟨e,he⟩ ⟨f,hf⟩ h
  rcases Sym2.eq_iff.mp h with ⟨hef,_⟩ | ⟨hef,_⟩
  · exact Subtype.ext hef
  · have hh := congrArg label hef
    rw [r.label_reverse,he,hf] at hh
    exact False.elim (hbar (label x) hh.symm)

/-- Switching two edges disjoint from the prior prescriptions preserves them. -/
theorem switch_contains (r : Matching label bar) (C : Finset (Sym2 D))
    (hC : r.Contains C) (x e : D) (he : label x = label e)
    (hxC : s(x,r x) ∉ C) (heC : s(e,r e) ∉ C) : (r.switch x e he).Contains C := by
  intro a b hab
  have hr := hC a b hab
  have hax : a ≠ x := by intro h; subst a; exact hxC (hr ▸ hab)
  have hae : a ≠ e := by intro h; subst a; exact heC (hr ▸ hab)
  have hbx : b ≠ x := by
    intro h
    have hra : r x = a := by rw [← h,← hr,r.reverse_reverse]
    exact hxC (by simpa only [hra,h,Sym2.eq_swap] using hab)
  have hbe : b ≠ e := by
    intro h
    have hra : r e = a := by rw [← h,← hr,r.reverse_reverse]
    exact heC (by simpa only [hra,h,Sym2.eq_swap] using hab)
  simp only [switch_apply,Equiv.swap_apply_of_ne_of_ne hax hae,hr,
    Equiv.swap_apply_of_ne_of_ne hbx hbe]

variable [Fintype V] [Fintype D]

/-- All allowed transpositions for the distinguished port, omitting prior
edges and both radius-R endpoint balls. -/
def admissible (r : Matching label bar) (origin : D → V) (x : D)
    (R : ℕ) (C : Finset (Sym2 D)) : Finset {e : D // label e = label x} := by
  classical
  let Γ := r.graph origin
  let B := ball (graphNeighbors Γ.subdivision) (Sum.inr x) R ∪
    ball (graphNeighbors Γ.subdivision) (Sum.inr (r x)) R
  exact Finset.univ.filter fun e => s(e.val,r e.val) ∉ C ∧
    Sum.inr e.val ∉ B ∧ Sum.inr (r e.val) ∉ B

/-- The excluded prior set costs exactly one port per prior edge, not two. -/
theorem admissible_card (r : Matching label bar) (origin : D → V)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (x : D) (R : ℕ) (C : Finset (Sym2 D)) :
    Nat.card {e : D // label e = label x} - C.card - 4*d^(R+1) ≤
      (r.admissible origin x R C).card := by
  classical
  let X := {e : D // label e = label x}
  let P : Finset X := Finset.univ.filter fun e => s(e.val,r e.val) ∈ C
  have hP : P.card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun e : X => s(e.val,r e.val))
    · intro e he; exact (Finset.mem_filter.mp he).2
    · exact (r.edge_name_injective x hbar).injOn
  have hbound := BallCount.admissible_card (Equiv.refl X)
    (fun e : X => (Sum.inr e.val : V ⊕ D)) (fun e : X => (Sum.inr (r e.val) : V ⊕ D))
    (by intro a b h; exact Subtype.ext (Sum.inr.inj h))
    (by intro a b h; exact Subtype.ext (r.val.injective (Sum.inr.inj h)))
    (graphNeighbors (r.graph origin).subdivision) d h2
    (subdivision_degree (r.graph origin) d h2 hd) (Sum.inr x) (Sum.inr (r x)) R P
  have ht : Fintype.card X - P.card - 4*d^(R+1) ≤
      (r.admissible origin x R C).card := by
    convert hbound using 1
    congr 1
    ext e
    simp [admissible,P]
  rw [Nat.card_eq_fintype_card]
  exact (Nat.sub_le_sub_right (Nat.sub_le_sub_left hP _) _).trans ht

/-- The girth condition is preserved by each counted auxiliary port. -/
theorem admissible_preserves (r : Matching label bar) (origin : D → V)
    (x : D) (N : ℕ) (C : Finset (Sym2 D))
    (hC : r.Contains C) (hxC : s(x,r x) ∉ C)
    (hg : (N : ℕ∞) ≤ (r.graph origin).subdivision.egirth)
    (e : {e : D // label e = label x}) (he : e ∈ r.admissible origin x (2*N) C) :
    (r.switch x e.val e.property.symm).Contains C ∧
      (N : ℕ∞) ≤ ((r.switch x e.val e.property.symm).graph origin).subdivision.egirth := by
  classical
  have he' := Finset.mem_filter.mp he |>.2
  change s(e.val,r e.val) ∉ C ∧ _ at he'
  have hfar : ∀ a ∈ ({Sum.inr x,Sum.inr (r x)} : Set (V ⊕ D)),
      ∀ b ∈ ({Sum.inr e.val,Sum.inr (r e.val)} : Set (V ⊕ D)),
      ∀ p : (r.graph origin).subdivision.Walk a b, 2*N < p.length := by
    intro a ha b hb p
    apply far_of_not_mem_ball (r.graph origin).subdivision (2*N) _ p
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun h => he'.2.1 (Finset.mem_union_left _ h)
    · exact fun h => he'.2.2 (Finset.mem_union_left _ h)
    · exact fun h => he'.2.1 (Finset.mem_union_right _ h)
    · exact fun h => he'.2.2 (Finset.mem_union_right _ h)
  have far_ne {a b : V ⊕ D}
      (hf : ∀ p : (r.graph origin).subdivision.Walk a b, 2*N < p.length) : a ≠ b := by
    intro h
    subst b
    have hh := hf SimpleGraph.Walk.nil
    simp at hh
  have hxe : x ≠ e.val := by
    intro h
    exact far_ne (hfar (.inr x) (by simp) (.inr e.val) (by simp)) (congrArg Sum.inr h)
  have hxr : x ≠ r e.val := by
    intro h
    exact far_ne (hfar (.inr x) (by simp) (.inr (r e.val)) (by simp)) (congrArg Sum.inr h)
  refine ⟨r.switch_contains C hC x e.val e.property.symm hxC he'.1,?_⟩
  rw [graph_switch,subdivision_switch (r.graph origin) x e.val hxe hxr]
  exact girth_switch N hg rfl hfar

/-- Direct double counting on the whole tuple space, with all other matchings
retained in the output. No independence after conditioning is used. -/
theorem conditioned_count (origin : D → V) (N : ℕ) (C : Finset (Sym2 D))
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (x y : D) (hxy : s(x,y) ∉ C) :
    ((conditioned (label := label) (bar := bar) origin N C).filter (fun r => r x = y)).card *
      (Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1)) ≤
      (conditioned (label := label) (bar := bar) origin N C).card := by
  classical
  let Ω := conditioned (label := label) (bar := bar) origin N C
  let r₀ := Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1)
  let F := {r : Matching label bar // r ∈ Ω ∧ r x = y}
  let S := (r : F) × {e : {e : D // label e = label x} //
    e ∈ r.val.admissible origin x (2*N) C}
  have hm (r : F) : r.val.Contains C ∧
      (N : ℕ∞) ≤ (r.val.graph origin).subdivision.egirth := by
    have h := r.property.1
    simpa only [Ω,conditioned,Finset.mem_filter,Finset.mem_univ,true_and] using h
  let out : S → {r : Matching label bar // r ∈ Ω} := fun p =>
    ⟨p.1.val.switch x p.2.val.val p.2.val.property.symm,by
      have hh := p.1.val.admissible_preserves origin x N C (hm p.1).1
        (by simpa only [p.1.property.2] using hxy) (hm p.1).2 p.2.val p.2.property
      simpa only [Ω,conditioned,Finset.mem_filter,Finset.mem_univ,true_and] using hh⟩
  have hout : Function.Injective out := by
    intro p q h
    have hs : p.1.val.switch x p.2.val.val p.2.val.property.symm =
        q.1.val.switch x q.2.val.val q.2.val.property.symm := congrArg Subtype.val h
    have hi := switch_injective (label := label) (bar := bar) x y hbar
      (a₁ := (⟨p.1.val,p.1.property.2⟩,⟨p.2.val.val,p.2.val.property.symm⟩))
      (a₂ := (⟨q.1.val,q.1.property.2⟩,⟨q.2.val.val,q.2.val.property.symm⟩)) hs
    have hr : p.1 = q.1 := Subtype.ext (congrArg (fun z => z.1.val) hi)
    cases p with
    | mk r e =>
      cases q with
      | mk s f =>
        dsimp at hr
        subst s
        have hef : e = f := Subtype.ext (Subtype.ext (congrArg (fun z => z.2.val) hi))
        subst f
        rfl
  have hc := Fintype.card_le_of_injective out hout
  have hsource : Fintype.card S = ∑ r : F, (r.val.admissible origin x (2*N) C).card := by
    simp only [S,Fintype.card_sigma,Fintype.card_coe]
  have htarget : Fintype.card {r : Matching label bar // r ∈ Ω} = Ω.card := Fintype.card_coe Ω
  have hF : Fintype.card F = (Ω.filter (fun r => r x = y)).card := by
    change Fintype.card {r : Matching label bar // r ∈ Ω ∧ r x = y} = _
    rw [Fintype.card_subtype]
    congr 1
    ext r
    simp
  have hsum : Fintype.card F * r₀ ≤ ∑ r : F, (r.val.admissible origin x (2*N) C).card := by
    calc
      Fintype.card F * r₀ = ∑ _r : F, r₀ := by simp
      _ ≤ ∑ r : F, (r.val.admissible origin x (2*N) C).card :=
        Finset.sum_le_sum fun r _ => r.val.admissible_card origin hbar d h2 hd x (2*N) C
  rw [hsource,htarget] at hc
  rw [hF] at hsum
  exact hsum.trans hc

omit [Fintype D] in
/-- Adding one undirected prescription is exactly one matching-coordinate
condition; the reverse orientation is automatic, not an extra constraint. -/
theorem contains_insert (r : Matching label bar) (C : Finset (Sym2 D)) (x y : D) :
    r.Contains (insert s(x,y) C) ↔ r.Contains C ∧ r x = y := by
  classical
  constructor
  · intro h
    exact ⟨fun a b hab => h a b (Finset.mem_insert_of_mem hab),h x y (by simp)⟩
  · rintro ⟨hC,hxy⟩ a b hab
    rcases Finset.mem_insert.mp hab with h | h
    · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hxy
      · rw [← hxy,r.reverse_reverse]
    · exact hC a b h

omit [Fintype V] in
theorem conditioned_insert (origin : D → V) (N : ℕ) (C : Finset (Sym2 D))
    (x y : D) :
    conditioned (label := label) (bar := bar) origin N (insert s(x,y) C) =
      (conditioned (label := label) (bar := bar) origin N C).filter (fun r => r x = y) := by
  classical
  ext r
  simp only [conditioned,Finset.mem_filter,Finset.mem_univ,true_and,contains_insert]
  tauto

/-- The simultaneous-prescription bound obtained by successive conditioning.
No independence is asserted, even for prescriptions on distinct labels. -/
theorem prescriptions_count (origin : D → V) (N : ℕ)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (R : ℕ) (C : Finset (Sym2 D))
    (hR : ∀ x, R + C.card + 4*d^(2*N+1) ≤ Nat.card {e : D // label e = label x}) :
    (conditioned (label := label) (bar := bar) origin N C).card * R^C.card ≤
      (conditioned (label := label) (bar := bar) origin N ∅).card := by
  classical
  induction C using Finset.induction with
  | empty => simp
  | @insert e C he ih =>
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hR' : ∀ z, R + C.card + 4*d^(2*N+1) ≤
          Nat.card {e : D // label e = label z} := by
        intro z
        have hh := hR z
        rw [Finset.card_insert_of_notMem he] at hh
        omega
      have hstep := conditioned_count (label := label) (bar := bar)
        origin N C hbar d h2 hd x y he
      have hsmall : R ≤ Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1) := by
        have := hR' x
        omega
      have hstep' : (conditioned (label := label) (bar := bar) origin N (insert s(x,y) C)).card * R ≤
          (conditioned (label := label) (bar := bar) origin N C).card := by
        rw [conditioned_insert]
        exact (Nat.mul_le_mul_left _ hsmall).trans hstep
      rw [Finset.card_insert_of_notMem he,pow_succ,← mul_assoc,mul_right_comm]
      exact (Nat.mul_le_mul_right _ hstep').trans (ih hR')

end Matching
end TorsionFreeZeroDivisors.ConditionedMatchings

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternCount
open scoped Classical
open ConditionedMatchings
variable {V D T F E A : Type*} [Fintype V] [Fintype D] [Fintype F] [Fintype E]
variable (label : D → T) (bar : T → T)

omit [Fintype D] in
/-- A prescribed undirected edge can be read in either orientation. -/
theorem contains_prescriptions (r : Matching label bar) (ports : E → D × D) :
    r.Contains (Finset.univ.image (fun e => s((ports e).1,(ports e).2))) ↔
      ∀ e, r (ports e).1 = (ports e).2 := by
  classical
  constructor
  · intro h e
    exact h _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
  · intro h a b hab
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hab
    rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [← ha,← hb,h]
    · rw [← ha,← hb,← h e,r.reverse_reverse]

omit [Fintype V] in
/-- The expectation numerator counts each vertex realization in each matching
exactly once; prescriptions retain every edge, rather than path occurrences. -/
theorem sum_realizations_eq (origin : D → V) (N : ℕ) (C : F → Finset (Sym2 D)) :
    (∑ r ∈ Matching.conditioned (label := label) (bar := bar) origin N ∅,
      (Finset.univ.filter (fun f : F => r.Contains (C f))).card) =
    ∑ f : F, (Matching.conditioned (label := label) (bar := bar) origin N (C f)).card := by
  classical
  let Ω := Matching.conditioned (label := label) (bar := bar) origin N ∅
  have hcf (f : F) : Matching.conditioned (label := label) (bar := bar) origin N (C f) =
      Ω.filter (fun r => r.Contains (C f)) := by
    ext r
    simp only [Matching.conditioned,Ω,Finset.mem_filter,Finset.mem_univ,true_and]
    have hemp : r.Contains (∅ : Finset (Sym2 D)) := by intro a b h; simp at h
    tauto
  simp_rw [hcf,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- Finite first-moment bound for a fixed labelled actual-image pattern.
Distinct edges, not occurrences, supply the power of the matching denominator. -/
theorem expectation_bound [DecidableEq D] (origin : D → V) (N : ℕ)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (C : F → Finset (Sym2 D)) (E R : ℕ) (hcard : ∀ f, (C f).card = E)
    (hR : 0 < R)
    (hsize : ∀ x, R + E + 4*d^(2*N+1) ≤ Nat.card {e : D // label e = label x})
    (hΩ : (Matching.conditioned (label := label) (bar := bar) origin N ∅).Nonempty) :
    ((∑ r ∈ Matching.conditioned (label := label) (bar := bar) origin N ∅,
        (Finset.univ.filter (fun f : F => r.Contains (C f))).card : ℕ) : ℝ) /
      (Matching.conditioned (label := label) (bar := bar) origin N ∅).card ≤
      (Fintype.card F : ℝ) / (R : ℝ)^E := by
  classical
  let Ω := Matching.conditioned (label := label) (bar := bar) origin N ∅
  have hcount (f : F) : (Matching.conditioned (label := label) (bar := bar)
      origin N (C f)).card * R^E ≤ Ω.card := by
    have h := Matching.prescriptions_count (label := label) (bar := bar)
      origin N hbar d h2 hd R (C f) (by intro x; rw [hcard]; exact hsize x)
    simpa only [hcard] using h
  have hs : (∑ f : F, (Matching.conditioned (label := label) (bar := bar)
      origin N (C f)).card) * R^E ≤ Fintype.card F * Ω.card := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ _f : F, Ω.card := Finset.sum_le_sum (fun f _ => hcount f)
      _ = _ := by simp
  rw [sum_realizations_eq]
  have hs' : ((∑ f : F, (Matching.conditioned (label := label) (bar := bar)
      origin N (C f)).card : ℕ) : ℝ) * (R : ℝ)^E ≤ (Fintype.card F : ℝ) * Ω.card := by
    exact_mod_cast hs
  have hp : (0 : ℝ) < (R : ℝ)^E := pow_pos (Nat.cast_pos.mpr hR) _
  have ho : (0 : ℝ) < Ω.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hΩ)
  exact (div_le_div_iff₀ ho hp).mpr hs'

/-- Independent vertex carrier restrictions count by an exact product. This
is an upper bound for injective vertex maps, without assuming independence
of sampled edges. -/
theorem vertex_assignments_card [Fintype A]
    (allowed : A → Finset V) :
    Fintype.card {f : A → V // ∀ a, f a ∈ allowed a} =
      ∏ a : A, (allowed a).card := by
  classical
  let e : {f : A → V // ∀ a, f a ∈ allowed a} ≃ ((a : A) → {v : V // v ∈ allowed a}) :=
    { toFun := fun f a => ⟨f.val a,f.property a⟩
      invFun := fun f => ⟨fun a => (f a).val,fun a => (f a).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_pi]
  simp only [Fintype.card_coe]

end TorsionFreeZeroDivisors.PatternCount

namespace TorsionFreeZeroDivisors.PatternEmbeddings
open scoped BigOperators Classical
open PortSubdivision ConditionedMatchings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

def edges (Γ : PortGraph PV PD) : Finset (Sym2 PD) :=
  Finset.univ.image (fun d => s(d,Γ.reverse d))

abbrev VertexMap (allowed : PV → Finset TV) :=
  {f : PV → TV // Function.Injective f ∧ ∀ v, f v ∈ allowed v}

variable (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
  (allowed : PV → Finset TV)
  (hallowed : ∀ v x, x ∈ allowed v → ∀ d, Γ.origin d = v → plabel d ∈ outgoing x)

/-- Every candidate is injective on actual-image vertices; the letters uniquely
specify the target ports before the random matching is chosen. -/
def dartMap (f : VertexMap allowed) (d : PD) : Dart outgoing :=
  ⟨(f.val (Γ.origin d),plabel d),hallowed _ _ (f.property.2 _) d rfl⟩

omit [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T] in
theorem dartMap_injective
    (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (f : VertexMap allowed) : Function.Injective (dartMap Γ plabel outgoing allowed hallowed f) := by
  intro d e he
  have hp := congrArg Subtype.val he
  have hv : Γ.origin d = Γ.origin e := f.property.1 (congrArg Prod.fst hp)
  have hl : plabel d = plabel e := congrArg Prod.snd hp
  exact himm (Prod.ext hv hl)

/-- Each undirected actual edge is prescribed once, regardless of its number
of occurrences in the paths. This prevents the independence fallacy. -/
def prescriptions (f : VertexMap allowed) : Finset (Sym2 (Dart outgoing)) :=
  (edges Γ).image (Sym2.map (dartMap Γ plabel outgoing allowed hallowed f))

omit [Fintype PV] [Fintype TV] [Fintype T] in
theorem prescriptions_card
    (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (f : VertexMap allowed) :
    (prescriptions Γ plabel outgoing allowed hallowed f).card = (edges Γ).card := by
  exact Finset.card_image_of_injective _ (Sym2.map.injective
    (dartMap_injective Γ plabel outgoing allowed hallowed himm f))

omit [Fintype PV] [Fintype TV] [Fintype T] in
/-- A matching contains the prescriptions precisely when the vertex map is
an edge-respecting labelled graph embedding. -/
theorem contains_iff (bar : T → T) (f : VertexMap allowed)
    (r : Matching (label outgoing) bar) :
    r.Contains (prescriptions Γ plabel outgoing allowed hallowed f) ↔
      ∀ d, r.val (dartMap Γ plabel outgoing allowed hallowed f d) =
        dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse d) := by
  have he : prescriptions Γ plabel outgoing allowed hallowed f =
      Finset.univ.image (fun d => s(dartMap Γ plabel outgoing allowed hallowed f d,
        dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse d))) := by
    rw [prescriptions,edges,Finset.image_image]
    rfl
  rw [he]
  convert PatternCount.contains_prescriptions (label outgoing) bar r
    (fun d => (dartMap Γ plabel outgoing allowed hallowed f d,
      dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse d))) using 1
  simp only [Matching.Contains,Finset.mem_image]

omit [Fintype PD] [Fintype T] in
theorem vertexMap_card : Fintype.card (VertexMap allowed) ≤ ∏ v, (allowed v).card := by
  let forget : VertexMap allowed → {f : PV → TV // ∀ v, f v ∈ allowed v} :=
    fun f => ⟨f.val,f.property.2⟩
  calc
    _ ≤ Fintype.card {f : PV → TV // ∀ v, f v ∈ allowed v} :=
      Fintype.card_le_of_injective forget (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : {f : PV → TV // ∀ v, f v ∈ allowed v} => z.val) h)
    _ = _ := PatternCount.vertex_assignments_card allowed

/-- Fixed-label stage first moment with all graph-embedding hypotheses
explicit. The only counting input on vertices is their literal carrier sets. -/
theorem expectation_bound (bar : T → T) (hbar : ∀ t, bar t ≠ t)
    (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : Dart outgoing // origin outgoing e = v} ≤ d)
    (hsize : ∀ x : Dart outgoing,
      R + (edges Γ).card + 4*d^(2*N+1) ≤
        Nat.card {e : Dart outgoing // label outgoing e = label outgoing x})
    (hΩ : (Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅).Nonempty) :
    ((∑ r ∈ Matching.conditioned (label := label outgoing) (bar := bar) (origin outgoing) N ∅,
      (Finset.univ.filter (fun f : VertexMap allowed =>
        ∀ e, r.val (dartMap Γ plabel outgoing allowed hallowed f e) =
          dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse e))).card : ℕ) : ℝ) /
      (Matching.conditioned (label := label outgoing) (bar := bar) (origin outgoing) N ∅).card ≤
        (∏ v, ((allowed v).card : ℝ)) / (R : ℝ) ^ (edges Γ).card := by
  have hc := PatternCount.expectation_bound (label outgoing) bar (origin outgoing) N hbar d h2 hd
    (prescriptions Γ plabel outgoing allowed hallowed) (edges Γ).card R
    (prescriptions_card Γ plabel outgoing allowed hallowed himm) hR hsize hΩ
  simp_rw [contains_iff] at hc
  refine hc.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  exact_mod_cast vertexMap_card allowed

end TorsionFreeZeroDivisors.PatternEmbeddings

/-!
Exact finite geometry and type system over the field with 128 elements.
-/

namespace TorsionFreeZeroDivisors
namespace Types

open scoped LinearAlgebra.Projectivization
open Configuration

instance : DecidableEq Field128 := Classical.decEq _

theorem order_eq : ProjectivePlane.order Point Line = 128 := by
  have h := ProjectivePlane.card_points Point Line
  rw [point_card] at h
  have hi : (16513 : ℤ) = (ProjectivePlane.order Point Line : ℤ) ^ 2 +
      (ProjectivePlane.order Point Line : ℤ) + 1 := by exact_mod_cast h
  have hf : ((ProjectivePlane.order Point Line : ℤ) - 128) *
      ((ProjectivePlane.order Point Line : ℤ) + 129) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h1 | h1 <;> omega

def linesOn (p : Point) : Finset Line := Finset.univ.filter (p ∈ ·)

@[simp] theorem mem_pointsOn {p : Point} {l : Line} : p ∈ pointsOn l ↔ p ∈ l := by
  simp [pointsOn]

@[simp] theorem mem_linesOn {p : Point} {l : Line} : l ∈ linesOn p ↔ p ∈ l := by
  simp [linesOn]

theorem pointsOn_card (l : Line) : (pointsOn l).card = 129 := by
  have h := ProjectivePlane.pointCount_eq Point l
  rw [order_eq] at h
  simpa [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, pointsOn] using h

theorem linesOn_card (p : Point) : (linesOn p).card = 129 := by
  have h := ProjectivePlane.lineCount_eq Line p
  rw [order_eq] at h
  simpa [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype, linesOn] using h

theorem linesOn_inter_card {p q : Point} (hpq : p ≠ q) :
    (linesOn p ∩ linesOn q).card = 1 := by
  obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line Point Line p q hpq
  have heq : linesOn p ∩ linesOn q = {l} := by
    ext m
    simp only [Finset.mem_inter, mem_linesOn, Finset.mem_singleton]
    exact ⟨fun hm => hu m hm, fun hm => hm ▸ hl⟩
  rw [heq, Finset.card_singleton]

/-- Counting a predicate depending only on the first coordinate. -/
theorem card_prod_fst {U V : Type*} [Fintype U] [Fintype V]
    (p : U → Prop) [DecidablePred p] :
    Fintype.card {x : U × V // p x.1} = Fintype.card {u : U // p u} * Fintype.card V := by
  let e : {x : U × V // p x.1} ≃ {u : U // p u} × V :=
    { toFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
      invFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

theorem card_prod_snd {U V : Type*} [Fintype U] [Fintype V]
    (p : V → Prop) [DecidablePred p] :
    Fintype.card {x : U × V // p x.2} = Fintype.card U * Fintype.card {v : V // p v} := by
  let e : {x : U × V // p x.2} ≃ U × {v : V // p v} :=
    { toFun := fun x => (x.val.1, ⟨x.val.2, x.property⟩)
      invFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

/-! The empirical type slots. Each line has exactly 33026 slots on each
side, before the admissible replication parameter is applied. -/

theorem card_slotA : Fintype.card SlotA = 33026 := by
  simp [SlotA]

theorem card_slotB : Fintype.card SlotB = 33026 := by
  simp [SlotB]

theorem card_vertexA (N : ℕ) : Fintype.card (VertexA N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotA, Fintype.card_fin, point_card]
  ring

theorem card_vertexB (N : ℕ) : Fintype.card (VertexB N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotB, Fintype.card_fin, point_card]
  ring

theorem degreeA_bounds {N : ℕ} (x : VertexA N) :
    129 ≤ (outgoingA x).card ∧ (outgoingA x).card ≤ 132 := by
  rw [outgoingA, Finset.card_disjSum, pointsOn_card]
  rcases x.2.1 with ⟨i,j⟩ | k <;> simp [extrasA, Finset.card_erase_of_mem]

theorem degreeB_bounds {N : ℕ} (y : VertexB N) :
    129 ≤ (outgoingB y).card ∧ (outgoingB y).card ≤ 132 := by
  rw [outgoingB, Finset.card_disjSum, pointsOn_card]
  cases y.2.1 <;> simp [extrasB]

theorem slotA_extra_frequency (e : Fin 3) :
    Fintype.card {a : SlotA // e ∈ extrasA a} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have hz : (∑ a : Fin 32639, if e ∈ extrasA (.inr a) then 1 else 0) = 0 := by
    simp [extrasA]
  rw [hz, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 3) :
      (∑ j : Fin 129, if e ∈ extrasA (.inl (i,j)) then 1 else 0) =
        129 * (if e ≠ i then 1 else 0) := by
    by_cases h : e = i <;> simp [extrasA, h]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hc : (Finset.univ.filter fun i : Fin 3 => e ≠ i) = Finset.univ.erase e := by ext i; simp [ne_comm]
  rw [hc]
  simp

theorem slotB_extra_frequency (e : Fin 3) :
    Fintype.card {b : SlotB // e ∈ extrasB b} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp [extrasB]

/-- Each of the 16516 letters has exactly np carriers on each side. -/
theorem letter_frequencyA (N : ℕ) (t : Letter) :
    Fintype.card {x : VertexA N // t ∈ outgoingA x} = 4260354 * N := by
  cases t with
  | inl p =>
    have he : (fun x : VertexA N => Sum.inl p ∈ outgoingA x) =
        (fun x => p ∈ x.1) := by funext x; simp [outgoingA]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_fst (V := SlotA × Fin N) (fun l : Line => p ∈ l), Fintype.card_prod, card_slotA, Fintype.card_fin]
    have hc : Fintype.card {l : Line // p ∈ l} = 129 := by
      rw [Fintype.card_subtype]
      exact linesOn_card p
    rw [hc]
    ring
  | inr e =>
    have he : (fun x : VertexA N => Sum.inr e ∈ outgoingA x) =
        (fun x => e ∈ extrasA x.2.1) := by funext x; simp [outgoingA]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_snd (U := Line) (fun x : SlotA × Fin N => e ∈ extrasA x.1),
      card_prod_fst (V := Fin N) (fun a : SlotA => e ∈ extrasA a),
      point_card, slotA_extra_frequency,
      Fintype.card_fin]
    ring

theorem letter_frequencyB (N : ℕ) (t : Letter) :
    Fintype.card {x : VertexB N // t ∈ outgoingB x} = 4260354 * N := by
  cases t with
  | inl p =>
    have he : (fun x : VertexB N => Sum.inl p ∈ outgoingB x) =
        (fun x => p ∈ x.1) := by funext x; simp [outgoingB]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_fst (V := SlotB × Fin N) (fun l : Line => p ∈ l), Fintype.card_prod, card_slotB, Fintype.card_fin]
    have hc : Fintype.card {l : Line // p ∈ l} = 129 := by
      rw [Fintype.card_subtype]
      exact linesOn_card p
    rw [hc]
    ring
  | inr e =>
    have he : (fun x : VertexB N => Sum.inr e ∈ outgoingB x) =
        (fun x => e ∈ extrasB x.2.1) := by funext x; simp [outgoingB]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_snd (U := Line) (fun x : SlotB × Fin N => e ∈ extrasB x.1),
      card_prod_fst (V := Fin N) (fun b : SlotB => e ∈ extrasB b),
      point_card, slotB_extra_frequency,
      Fintype.card_fin]
    ring

/-! ### The fixed inverse pairing and the actual space of graph matchings -/

@[simp] theorem inverse_signed (g : Generator) (b : Bool) :
    inverse (signedLetter (g,b)) = signedLetter (g,!b) := by simp [inverse]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  simp

theorem inverse_ne (t : Letter) : inverse t ≠ t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  intro he
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false] at he <;>
    cases signedLetter.injective he

variable {V : Type*} (outgoing : V → Finset Letter)

/-- Each inverse pair receives a bijection between its two carrier sets. -/
def MatchingTuple := (g : Generator) →
  {x : V // signedLetter (g,true) ∈ outgoing x} ≃
    {x : V // signedLetter (g,false) ∈ outgoing x}

/-- Exact empirical balance ensures the finite matching space is nonempty. -/
theorem matchingTuple_nonempty [Fintype V]
    (hfreq : ∀ t u, Fintype.card {x : V // t ∈ outgoing x} =
      Fintype.card {x : V // u ∈ outgoing x}) : Nonempty (MatchingTuple outgoing) := by
  exact ⟨fun g => Fintype.equivOfCardEq (hfreq _ _)⟩

/-- The direction of a step is given by the signed letter. Non-carrier
values are immaterial and are defined to fix the vertex. -/
def nextSigned (M : MatchingTuple outgoing) (x : V) : Signed → V
  | (g,true) => if hx : signedLetter (g,true) ∈ outgoing x then (M g ⟨x,hx⟩).val else x
  | (g,false) => if hx : signedLetter (g,false) ∈ outgoing x then ((M g).symm ⟨x,hx⟩).val else x

def next (M : MatchingTuple outgoing) (x : V) (t : Letter) : V :=
  nextSigned outgoing M x (signedLetter.symm t)

@[simp] theorem next_signed (M : MatchingTuple outgoing) (x : V) (g : Generator) (b : Bool) :
    next outgoing M x (signedLetter (g,b)) = nextSigned outgoing M x (g,b) := by
  simp [next]

theorem next_reverse_mem (M : MatchingTuple outgoing) (x : V) (t : Letter)
    (ht : t ∈ outgoing x) : inverse t ∈ outgoing (next outgoing M x t) := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false, next_signed]
  · simpa [nextSigned, ht] using ((M g).symm ⟨x,ht⟩).property
  · simpa [nextSigned, ht] using (M g ⟨x,ht⟩).property

theorem next_reverse_next (M : MatchingTuple outgoing) (x : V) (t : Letter)
    (ht : t ∈ outgoing x) : next outgoing M (next outgoing M x t) (inverse t) = x := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false, next_signed]
  · simp only [nextSigned, dif_pos ht]
    have hc := ((M g).symm ⟨x,ht⟩).property
    rw [dif_pos hc]
    exact congrArg Subtype.val ((M g).apply_symm_apply ⟨x,ht⟩)
  · simp only [nextSigned, dif_pos ht]
    have hc := (M g ⟨x,ht⟩).property
    rw [dif_pos hc]
    exact congrArg Subtype.val ((M g).symm_apply_apply ⟨x,ht⟩)

/-- In particular both source sides have an actual matching space. This
makes no girth or arrangement claim about a chosen point in that space. -/
theorem matchingA_nonempty (N : ℕ) : Nonempty (MatchingTuple (@outgoingA N)) :=
  matchingTuple_nonempty _ (fun t u => (letter_frequencyA N t).trans (letter_frequencyA N u).symm)

theorem matchingB_nonempty (N : ℕ) : Nonempty (MatchingTuple (@outgoingB N)) :=
  matchingTuple_nonempty _ (fun t u => (letter_frequencyB N t).trans (letter_frequencyB N u).symm)

/-! Joint type incidences for internal-chain vertex counts.
These derive the turn weights from the actual prescribed types. -/

theorem card_prod_both {U V : Type*} [Fintype U] [Fintype V]
    (p : U → Prop) (q : V → Prop) [DecidablePred p] [DecidablePred q] :
    Fintype.card {x : U × V // p x.1 ∧ q x.2} =
      Fintype.card {u : U // p u} * Fintype.card {v : V // q v} := by
  let e : {x : U × V // p x.1 ∧ q x.2} ≃ {u : U // p u} × {v : V // q v} :=
    { toFun := fun x => (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
      invFun := fun x => ⟨(x.1.val,x.2.val),⟨x.1.property,x.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

theorem slotA_extra_joint (e f : Fin 3) (hef : e ≠ f) :
    Fintype.card {a : SlotA // e ∈ extrasA a ∧ f ∈ extrasA a} = 129 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have hz : (∑ a : Fin 32639, if e ∈ extrasA (.inr a) ∧ f ∈ extrasA (.inr a)
      then 1 else 0) = 0 := by simp [extrasA]
  rw [hz, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 3) :
      (∑ j : Fin 129, if e ∈ extrasA (.inl (i,j)) ∧ f ∈ extrasA (.inl (i,j))
        then 1 else 0) = 129 * (if e ≠ i ∧ f ≠ i then 1 else 0) := by
    by_cases he : e = i <;> by_cases hf : f = i <;> simp [extrasA, he, hf]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hc : (Finset.univ.filter fun i : Fin 3 => e ≠ i ∧ f ≠ i).card = 1 := by
    have he : (Finset.univ.filter fun i : Fin 3 => e ≠ i ∧ f ≠ i) =
        (Finset.univ.erase e).erase f := by
      ext i
      simp [and_comm, ne_comm]
    rw [he, Finset.card_erase_of_mem (by simp [hef.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ e)]
    simp
  rw [hc]
  norm_num

theorem slotB_extra_joint (e f : Fin 3) :
    Fintype.card {b : SlotB // e ∈ extrasB b ∧ f ∈ extrasB b} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp [extrasB]

theorem line_single_card (p : Point) : Fintype.card {l : Line // p ∈ l} = 129 := by
  rw [Fintype.card_subtype]
  exact linesOn_card p

theorem line_joint_card (p q : Point) (hpq : p ≠ q) :
    Fintype.card {l : Line // p ∈ l ∧ q ∈ l} = 1 := by
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun l : Line => p ∈ l ∧ q ∈ l) =
      linesOn p ∩ linesOn q := by ext l; simp [linesOn]
  rw [he, linesOn_inter_card hpq]

/-- Counts of joint carriers can be computed in a general independent
line-slot-replica type, so both sides use literally the same geometry. -/
theorem joint_ordinary {S : Type*} [Fintype S] (extra : S → Finset (Fin 3))
    (N : ℕ) (p q : Point) (hpq : p ≠ q) :
    Fintype.card {x : Line × S × Fin N //
      Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
      Sum.inl q ∈ (pointsOn x.1).disjSum (extra x.2.1)} = Fintype.card S * N := by
  have he (x : Line × S × Fin N) :
      (Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
       Sum.inl q ∈ (pointsOn x.1).disjSum (extra x.2.1)) ↔ (p ∈ x.1 ∧ q ∈ x.1) := by
    simp
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    card_prod_fst (V := S × Fin N) (fun l : Line => p ∈ l ∧ q ∈ l),
    line_joint_card p q hpq, Fintype.card_prod, Fintype.card_fin, one_mul]

theorem joint_mixed {S : Type*} [Fintype S] (extra : S → Finset (Fin 3))
    (N : ℕ) (p : Point) (e : Fin 3) :
    Fintype.card {x : Line × S × Fin N //
      Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
      Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1)} =
      129 * Fintype.card {s : S // e ∈ extra s} * N := by
  have he (x : Line × S × Fin N) :
      (Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
       Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1)) ↔
      (p ∈ x.1 ∧ e ∈ extra x.2.1) := by simp
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    card_prod_both (fun l : Line => p ∈ l) (fun x : S × Fin N => e ∈ extra x.1),
    card_prod_fst (V := Fin N) (fun s : S => e ∈ extra s), line_single_card p, Fintype.card_fin]
  ring

theorem joint_extras {S : Type*} [Fintype S] (extra : S → Finset (Fin 3))
    (N : ℕ) (e f : Fin 3) :
    Fintype.card {x : Line × S × Fin N //
      Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
      Sum.inr f ∈ (pointsOn x.1).disjSum (extra x.2.1)} =
      16513 * Fintype.card {s : S // e ∈ extra s ∧ f ∈ extra s} * N := by
  have he (x : Line × S × Fin N) :
      (Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
       Sum.inr f ∈ (pointsOn x.1).disjSum (extra x.2.1)) ↔
      (e ∈ extra x.2.1 ∧ f ∈ extra x.2.1) := by simp
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    card_prod_snd (U := Line) (fun x : S × Fin N => e ∈ extra x.1 ∧ f ∈ extra x.1),
    card_prod_fst (V := Fin N) (fun s : S => e ∈ extra s ∧ f ∈ extra s), point_card, Fintype.card_fin]
  ring

end Types
end TorsionFreeZeroDivisors

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors
namespace WordEstimate

open scoped BigOperators

def inverse (t : Letter) : Letter := (t.1, !t.2)

def IsExtra (t : Letter) : Prop := ∃ i : Fin 3, t = (Sum.inl i, true)

instance (t : Letter) : Decidable (IsExtra t) := inferInstanceAs (Decidable (∃ _, _))

@[simp] theorem isExtra_inl (i : Fin 3) (b : Bool) :
    IsExtra (Sum.inl i, b) ↔ b = true := by simp [IsExtra, Prod.mk.injEq]

@[simp] theorem not_isExtra_inr (i : Fin 8255) (b : Bool) :
    ¬IsExtra (Sum.inr i, b) := by simp [IsExtra]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  simp [inverse]

theorem inverse_ne (t : Letter) : inverse t ≠ t := by
  rcases t with ⟨i, b⟩
  cases b <;> simp [inverse]

theorem extra_inverse_not_extra (t : Letter) (h : IsExtra t) : ¬IsExtra (inverse t) := by
  obtain ⟨i, rfl⟩ := h
  simp [inverse]

/-- The exact marginal letter frequency `p=129/16513`. -/
def p : ℝ := 129 / 16513

/-- Conditional turn weights on side B before setting cancelling turns to zero. -/
def baseWeight (t u : Letter) : ℝ :=
  if IsExtra (inverse t) then (if IsExtra u then 1 else p)
  else (if IsExtra u then p else 1 / 129)

/-- Source `w(t,u)`, including zero on cancelling turns. -/
def weight (t u : Letter) : ℝ := if u = inverse t then 0 else baseWeight t u

/-- The positive test vector in the manuscript's matrix argument. -/
def f (t : Letter) : ℝ := if IsExtra (inverse t) then 5 else 1

theorem one_le_f (t : Letter) : 1 ≤ f t := by
  unfold f
  split_ifs <;> norm_num

theorem f_extra (t : Letter) (h : IsExtra t) : f t = 1 := by
  simp [f, extra_inverse_not_extra t h]

theorem sum_f : (∑ t : Letter, f t) = 16528 := by
  simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type,
    f, inverse]
  norm_num

/-- The two row types have the exact untruncated mass given by the source. -/
theorem base_row_mass (t : Letter) :
    (∑ u : Letter, baseWeight t u ^ 2 * f u) =
      if IsExtra (inverse t) then 3 + 16525 * p ^ 2
      else 3 * p ^ 2 + 16525 / 129 ^ 2 := by
  unfold baseWeight
  split_ifs with h
  · simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type,
      f, inverse]
    ring
  · simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type,
      f, inverse]
    ring

/-- Removing the cancelling turn removes precisely its diagonal summand. -/
theorem row_mass (t : Letter) :
    (∑ u : Letter, weight t u ^ 2 * f u) =
      (∑ u : Letter, baseWeight t u ^ 2 * f u) -
        baseWeight t (inverse t) ^ 2 * f (inverse t) := by
  classical
  have h (u : Letter) : weight t u ^ 2 * f u =
      baseWeight t u ^ 2 * f u -
        if u = inverse t then baseWeight t u ^ 2 * f u else 0 := by
    by_cases hu : u = inverse t <;> simp [weight, hu]
  simp_rw [h, Finset.sum_sub_distrib]
  simp

/-- `Mf ≤ (149/150)f`, with the exact alphabet, weights and constants. -/
theorem matrix_contraction (t : Letter) :
    (∑ u : Letter, weight t u ^ 2 * f u) ≤ (149 / 150 : ℝ) * f t := by
  rw [row_mass, base_row_mass]
  by_cases h : IsExtra (inverse t)
  · have hfi : f (inverse t) = 1 := f_extra _ h
    have hft : f t = 5 := by simp [f, h]
    simp only [h, ite_true, baseWeight, hfi, hft]
    norm_num [p]
  · have hf := one_le_f (inverse t)
    have hft : f t = 1 := by simp [f, h]
    simp only [h, ite_false, baseWeight, hft]
    norm_num [p]
    nlinarith

/-- Product of the turn weights from a starting letter through a tail. -/
def continuation : (n : ℕ) → Letter → (Fin n → Letter) → ℝ
  | 0, _, _ => 1
  | n + 1, t, W => weight t (W 0) * continuation n (W 0) (Fin.tail W)

/-- Source `P(W)`, with empty products equal to one. -/
def wordWeight : (h : ℕ) → (Fin h → Letter) → ℝ
  | 0, _ => 1
  | h + 1, W => continuation h (W 0) (Fin.tail W)

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Letter) → ℝ) :
    (∑ W, F W) = ∑ t, ∑ W, F (Fin.cons t W) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Letter)).sum_comp F]
  rw [Fintype.sum_prod_type]
  rfl

/-- Iterating the exact matrix contraction controls all tails simultaneously. -/
theorem continuation_mass (n : ℕ) (t : Letter) :
    (∑ W : Fin n → Letter, continuation n t W ^ 2) ≤
      (149 / 150 : ℝ) ^ n * f t := by
  induction n generalizing t with
  | zero => simpa [continuation] using one_le_f t
  | succ n ih =>
    rw [sum_cons]
    simp only [continuation, Fin.cons_zero, Fin.tail_cons, mul_pow]
    simp_rw [← Finset.mul_sum]
    calc
      ∑ u, weight t u ^ 2 * ∑ W : Fin n → Letter, continuation n u W ^ 2
          ≤ ∑ u, weight t u ^ 2 * ((149 / 150 : ℝ) ^ n * f u) := by
            apply Finset.sum_le_sum
            intro u _
            exact mul_le_mul_of_nonneg_left (ih u) (sq_nonneg _)
      _ = (149 / 150 : ℝ) ^ n * ∑ u, weight t u ^ 2 * f u := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
      _ ≤ (149 / 150 : ℝ) ^ n * ((149 / 150 : ℝ) * f t) := by
            apply mul_le_mul_of_nonneg_left (matrix_contraction t)
            positivity
      _ = (149 / 150 : ℝ) ^ (n + 1) * f t := by ring

/-- The matrix form of the squared-word estimate, before exponent conversion. -/
theorem squared_word_geometric_bound (h : ℕ) :
    (∑ W : Fin (h + 1) → Letter, wordWeight (h + 1) W ^ 2) ≤
      16528 * (149 / 150 : ℝ) ^ h := by
  rw [sum_cons]
  simp only [wordWeight, Fin.cons_zero, Fin.tail_cons]
  calc
    ∑ t, ∑ W : Fin h → Letter, continuation h t W ^ 2
        ≤ ∑ t, (149 / 150 : ℝ) ^ h * f t := by
          exact Finset.sum_le_sum fun t _ ↦ continuation_mass h t
    _ = 16528 * (149 / 150 : ℝ) ^ h := by
          rw [← Finset.mul_sum, sum_f]
          ring

theorem continuation_eq_product (n : ℕ) (t : Letter) (W : Fin n → Letter) :
    continuation n t W =
      ∏ i : Fin n, weight ((Fin.cons t W : Fin (n + 1) → Letter) i.castSucc)
        ((Fin.cons t W : Fin (n + 1) → Letter) i.succ) := by
  induction n generalizing t with
  | zero => simp [continuation]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp only [continuation, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
      ih]
    simp only [Fin.cons_self_tail, Fin.castSucc_succ, Fin.cons_succ, Fin.tail]

theorem wordWeight_eq_product (h : ℕ) (W : Fin (h + 1) → Letter) :
    wordWeight (h + 1) W = ∏ i : Fin h, weight (W i.castSucc) (W i.succ) := by
  rw [wordWeight, continuation_eq_product]
  simp only [Fin.cons_self_tail]

theorem constant_le_exp : (16528 : ℝ) ≤ Real.exp 10 := by
  calc
    (16528 : ℝ) ≤ (27 / 10 : ℝ) ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := by
      gcongr
      exact le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
    _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num

theorem ratio_le_exp : (149 / 150 : ℝ) ≤ Real.exp (-1 / 150) := by
  have h := Real.add_one_le_exp (-1 / 150)
  linarith

/-- The manuscript's exact numerical cutoff, without asymptotic weakening. -/
theorem geometric_exponential_bound (n : ℕ) (hn : 3001 ≤ n) :
    16528 * (149 / 150 : ℝ) ^ n ≤ Real.exp (-((n : ℝ) + 1) / 300) := by
  calc
    16528 * (149 / 150 : ℝ) ^ n
        ≤ Real.exp 10 * Real.exp (-1 / 150) ^ n := by
            apply mul_le_mul constant_le_exp
            · gcongr; exact ratio_le_exp
            · positivity
            · positivity
    _ = Real.exp (10 + (n : ℝ) * (-1 / 150)) := by
          rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp (-((n : ℝ) + 1) / 300) := by
          apply Real.exp_le_exp.mpr
          have hn' : (3001 : ℝ) ≤ n := by exact_mod_cast hn
          linarith

/-- Source lemma `lem:squared-words`, with its exhibited delta=1/600. -/
theorem squared_word_estimate (h : ℕ) (hh : 3002 ≤ h) :
    (∑ W : Fin h → Letter, wordWeight h W ^ 2) ≤
      Real.exp (-2 * (1 / 600 : ℝ) * h) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have hn : 3001 ≤ n := by omega
  have hbound := le_trans (squared_word_geometric_bound n)
    (geometric_exponential_bound n hn)
  apply hbound.trans_eq
  congr 1
  simp only [Nat.cast_succ]
  ring

/-! Binning the weights: entropy.tex, equation (entropy-bins). -/

theorem weight_nonneg (t u : Letter) : 0 ≤ weight t u := by
  unfold weight baseWeight p
  split_ifs <;> norm_num

theorem weight_le_one (t u : Letter) : weight t u ≤ 1 := by
  unfold weight baseWeight p
  split_ifs <;> norm_num

theorem weight_pos_lower (t u : Letter) (h : 0 < weight t u) :
    (1 / 129 : ℝ) ≤ weight t u := by
  unfold weight baseWeight p at *
  split_ifs at * <;> norm_num at *

theorem continuation_nonneg (n : ℕ) (t : Letter) (W : Fin n → Letter) :
    0 ≤ continuation n t W := by
  rw [continuation_eq_product]
  exact Finset.prod_nonneg fun _ _ => weight_nonneg _ _

theorem wordWeight_nonneg (h : ℕ) (W : Fin h → Letter) : 0 ≤ wordWeight h W := by
  cases h with
  | zero => norm_num [wordWeight]
  | succ h => exact continuation_nonneg _ _ _

theorem wordWeight_upper (h : ℕ) (hh : 3002 ≤ h) (W : Fin h → Letter) :
    wordWeight h W ≤ Real.exp (-(1 / 600 : ℝ) * h) := by
  have hsingle : wordWeight h W ^ 2 ≤
      ∑ V : Fin h → Letter, wordWeight h V ^ 2 :=
    Finset.single_le_sum (fun V _ => sq_nonneg (wordWeight h V)) (Finset.mem_univ W)
  have he := hsingle.trans (squared_word_estimate h hh)
  have hexp : Real.exp (-2 * (1 / 600 : ℝ) * h) =
      Real.exp (-(1 / 600 : ℝ) * h) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at he
  nlinarith [Real.exp_pos (-(1 / 600 : ℝ) * h)]

/-- Exact logarithmic bins, excluding zero weights just as in the source. -/
def binWords (h : ℕ) (d : ℤ) : Finset (Fin h → Letter) :=
  Finset.univ.filter fun W => 0 < wordWeight h W ∧ ⌊-Real.log (wordWeight h W)⌋ = d

theorem bin_sq_lower {h : ℕ} {d : ℤ} {W : Fin h → Letter}
    (hW : W ∈ binWords h d) :
    Real.exp (-2 * (d : ℝ) - 2) ≤ wordWeight h W ^ 2 := by
  obtain ⟨hp, hd⟩ := (Finset.mem_filter.mp hW).2
  have hfloor := Int.lt_floor_add_one (-Real.log (wordWeight h W))
  rw [hd] at hfloor
  have hlog : -2 * (d : ℝ) - 2 ≤ 2 * Real.log (wordWeight h W) := by linarith
  have he := Real.exp_le_exp.mpr hlog
  have hpow : Real.exp (2 * Real.log (wordWeight h W)) = wordWeight h W ^ 2 := by
    rw [show (2 : ℝ) * Real.log (wordWeight h W) =
      (2 : ℕ) * Real.log (wordWeight h W) by norm_num, Real.exp_nat_mul, Real.exp_log hp]
  rwa [hpow] at he

/-- The exact finite bin-count bound before replacing h by its common scale. -/
theorem bin_card_bound (h : ℕ) (hh : 3002 ≤ h) (d : ℤ) :
    ((binWords h d).card : ℝ) ≤
      Real.exp (2 * (d : ℝ) + 2 - 2 * (1 / 600 : ℝ) * h) := by
  have hlo : ((binWords h d).card : ℝ) * Real.exp (-2 * (d : ℝ) - 2) ≤
      ∑ W ∈ binWords h d, wordWeight h W ^ 2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun W hW => bin_sq_lower hW)
  have hsum : (∑ W ∈ binWords h d, wordWeight h W ^ 2) ≤
      ∑ W : Fin h → Letter, wordWeight h W ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun W _ _ => sq_nonneg _)
  have he := hlo.trans (hsum.trans (squared_word_estimate h hh))
  apply (le_div_iff₀ (Real.exp_pos _)).mpr at he
  apply he.trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Both the lower bin cutoff and the counting bound at the scalar block
scale s. The displayed threshold absorbs the manuscript's rounding errors. -/
theorem bin_scale_bounds (h : ℕ) (hh : 3002 ≤ h) (s : ℝ)
    (hscale : s + 1200 ≤ 2 * h) (d : ℤ) (W : Fin h → Letter)
    (hW : W ∈ binWords h d) :
    (1 / 600 : ℝ) * s / 2 ≤ (d : ℝ) ∧
      ((binWords h d).card : ℝ) ≤ Real.exp (2 * d - (1 / 600 : ℝ) * s) := by
  obtain ⟨hp, hd⟩ := (Finset.mem_filter.mp hW).2
  have hw := wordWeight_upper h hh W
  have hlog : Real.log (wordWeight h W) ≤ -(1 / 600 : ℝ) * h := by
    have he := Real.log_le_log hp hw
    simpa only [Real.log_exp] using he
  have hfloor := Int.lt_floor_add_one (-Real.log (wordWeight h W))
  rw [hd] at hfloor
  constructor
  · linarith
  · apply (bin_card_bound h hh d).trans
    apply Real.exp_le_exp.mpr
    linarith

end WordEstimate
end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.WordEstimate
open scoped BigOperators

/-- Every positive continuation has the uniform lower product bound from
its smallest allowed turn weight. -/
theorem continuation_lower (n : ℕ) (t : Letter) (W : Fin n → Letter)
    (hp : 0 < continuation n t W) :
    (1/129 : ℝ)^n ≤ continuation n t W := by
  induction n generalizing t with
  | zero => simp [continuation]
  | succ n ih =>
    dsimp [continuation] at hp ⊢
    have ht : 0 < weight t (W 0) := (mul_pos_iff.mp hp).elim (fun h => h.1)
      (fun h => False.elim (not_lt_of_ge (weight_nonneg _ _) h.1))
    have hu : 0 < continuation n (W 0) (fun i => W i.succ) :=
      (mul_pos_iff.mp hp).elim (fun h => h.2)
        (fun h => False.elim (not_lt_of_ge (weight_nonneg _ _) h.1))
    rw [pow_succ]
    exact mul_le_mul (ih _ _ hu) (weight_pos_lower _ _ ht) (by positivity)
      (continuation_nonneg _ _ _) |>.trans_eq (mul_comm _ _)

theorem wordWeight_lower (h : ℕ) (W : Fin h → Letter) (hp : 0 < wordWeight h W) :
    (1/129 : ℝ)^h ≤ wordWeight h W := by
  cases h with
  | zero => simp [wordWeight]
  | succ n =>
    have ht := continuation_lower n (W 0) (fun i => W i.succ) hp
    have hb : (1/129 : ℝ)^(n+1) ≤ (1/129 : ℝ)^n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (by norm_num)
    exact hb.trans ht

/-- A coarse fixed upper bin constant; the manuscript leaves a₀ unspecified.
We choose a₀=256, avoiding any numerical transcendental oracle. -/
theorem bin_upper_bound (h : ℕ) (s : ℝ) (hscale : (h : ℝ) ≤ 2*s)
    (d : ℤ) (W : Fin h → Letter) (hW : W ∈ binWords h d) : (d : ℝ) ≤ 256*s := by
  obtain ⟨hp,hd⟩ := (Finset.mem_filter.mp hW).2
  have ht := wordWeight_lower h W hp
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (1/129 : ℝ)^h) ht
  rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hl
  have hlog : Real.log (129 : ℝ) ≤ 128 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<129)
    norm_num at hh ⊢
    exact hh
  have hb := Int.floor_le (-Real.log (wordWeight h W))
  rw [hd] at hb
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg h : (0:ℝ)≤h)
  nlinarith

/-- Both bin cutoffs and the squared-word count with literal δ=1/600 and
one universal upper constant. -/
theorem bin_full_bounds (h : ℕ) (hh : 3002 ≤ h) (s : ℝ)
    (hscale : s+1200 ≤ 2*h) (hscale' : (h : ℝ) ≤ 2*s)
    (d : ℤ) (W : Fin h → Letter) (hW : W ∈ binWords h d) :
    (1/600 : ℝ)*s/2 ≤ d ∧ (d : ℝ) ≤ 256*s ∧
      ((binWords h d).card : ℝ) ≤ Real.exp (2*d-(1/600 : ℝ)*s) := by
  obtain ⟨hl,hc⟩ := bin_scale_bounds h hh s hscale d W hW
  exact ⟨hl,bin_upper_bound h s hscale' d W hW,hc⟩

end TorsionFreeZeroDivisors.WordEstimate

/-! Source entropy.tex 300--458, with all local root counts evaluated rather
than assumed. A translation self-link saves the root; a component without one
uses its selected bin-minimizing root. Reflection self-links are ruled out by
`BlockConstraints.reflection_impossible` before this count is applied. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypeWeights
open TorsionFreeZeroDivisors.Types

/-- The conditional joint-incidence table in the manuscript, before excluding
cancellation. Arguments here are the two outgoing letters at the vertex. -/
def jointWeight : Letter → Letter → ℝ
  | .inl _, .inl _ => 1/129
  | .inl _, .inr _ => 129/16513
  | .inr _, .inl _ => 129/16513
  | .inr _, .inr _ => 1

/-- The finite geometric incidence table equals the analytic table, without
changing the given inverse pairing or field. -/
theorem jointWeight_signed (t u : Signed) :
    jointWeight (inverse (signedLetter t)) (signedLetter u) = WordEstimate.baseWeight t u := by
  rw [show inverse (signedLetter t) = signedLetter (WordEstimate.inverse t) by
    rcases t with ⟨g,b⟩; exact inverse_signed g b]
  rcases t with ⟨i | i,b⟩ <;> rcases u with ⟨j | j,c⟩ <;>
    cases b <;> cases c <;>
    simp [signedLetter,jointWeight,WordEstimate.baseWeight,
      WordEstimate.inverse,WordEstimate.p]

/-- At an internal chain vertex of side B this is an exact count. -/
theorem joint_countB (rep : ℕ) (a b : Letter) (hab : a ≠ b) :
    (Fintype.card {v : VertexB rep // a ∈ outgoingB v ∧ b ∈ outgoingB v} : ℝ) =
      (Fintype.card (VertexB rep) : ℝ) * (129/16513) * jointWeight a b := by
  rw [card_vertexB]
  rcases a with p | e <;> rcases b with q | f
  · have hpq : p ≠ q := fun h => hab (congrArg Sum.inl h)
    rw [show Fintype.card {v : VertexB rep // Sum.inl p ∈ outgoingB v ∧ Sum.inl q ∈ outgoingB v} =
      33026*rep by simpa [outgoingB,card_slotB] using joint_ordinary extrasB rep p q hpq]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring
  · rw [show Fintype.card {v : VertexB rep // Sum.inl p ∈ outgoingB v ∧ Sum.inr f ∈ outgoingB v} =
      129*258*rep by simpa [outgoingB,slotB_extra_frequency] using joint_mixed extrasB rep p f]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring
  · have he' : Fintype.card {v : VertexB rep // Sum.inr e ∈ outgoingB v ∧ Sum.inl q ∈ outgoingB v} =
        Fintype.card {v : VertexB rep // Sum.inl q ∈ outgoingB v ∧ Sum.inr e ∈ outgoingB v} := by
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))
    rw [he',show Fintype.card {v : VertexB rep // Sum.inl q ∈ outgoingB v ∧ Sum.inr e ∈ outgoingB v} =
      129*258*rep by simpa [outgoingB,slotB_extra_frequency] using joint_mixed extrasB rep q e]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring
  · rw [show Fintype.card {v : VertexB rep // Sum.inr e ∈ outgoingB v ∧ Sum.inr f ∈ outgoingB v} =
      16513*258*rep by simpa [outgoingB,slotB_extra_joint] using joint_extras extrasB rep e f]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring

/-- The A-side conditional table is dominated by the B-side table, with the
source's factor 1/2 for distinct extras. -/
theorem joint_countA_le (rep : ℕ) (a b : Letter) (hab : a ≠ b) :
    (Fintype.card {v : VertexA rep // a ∈ outgoingA v ∧ b ∈ outgoingA v} : ℝ) ≤
      (Fintype.card (VertexA rep) : ℝ) * (129/16513) * jointWeight a b := by
  rw [card_vertexA]
  rcases a with p | e <;> rcases b with q | f
  · have hpq : p ≠ q := fun h => hab (congrArg Sum.inl h)
    rw [show Fintype.card {v : VertexA rep // Sum.inl p ∈ outgoingA v ∧ Sum.inl q ∈ outgoingA v} =
      33026*rep by simpa [outgoingA,card_slotA] using joint_ordinary extrasA rep p q hpq]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]
  · rw [show Fintype.card {v : VertexA rep // Sum.inl p ∈ outgoingA v ∧ Sum.inr f ∈ outgoingA v} =
      129*258*rep by simpa [outgoingA,slotA_extra_frequency] using joint_mixed extrasA rep p f]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]
  · rw [show Fintype.card {v : VertexA rep // Sum.inr e ∈ outgoingA v ∧ Sum.inl q ∈ outgoingA v} =
        Fintype.card {v : VertexA rep // Sum.inl q ∈ outgoingA v ∧ Sum.inr e ∈ outgoingA v} by
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))]
    rw [show Fintype.card {v : VertexA rep // Sum.inl q ∈ outgoingA v ∧ Sum.inr e ∈ outgoingA v} =
      129*258*rep by simpa [outgoingA,slotA_extra_frequency] using joint_mixed extrasA rep q e]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]
  · have hef : e ≠ f := fun h => hab (congrArg Sum.inr h)
    rw [show Fintype.card {v : VertexA rep // Sum.inr e ∈ outgoingA v ∧ Sum.inr f ∈ outgoingA v} =
      16513*129*rep by simpa [outgoingA,slotA_extra_joint e f hef] using joint_extras extrasA rep e f]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]

end TorsionFreeZeroDivisors.TypeWeights

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

/-- Actual vertex carriers: all outgoing template ports must be available;
`pin` imposes exactly the prescribed images, not extra random conditions. -/
def allowed (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
    (pin : PV → Option TV) (v : PV) : Finset TV :=
  Finset.univ.filter fun x => (∀ d, Γ.origin d = v → plabel d ∈ outgoing x) ∧
    ∀ y, pin v = some y → x = y

omit [Fintype PV] [Fintype T] in
theorem allowed_ports (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) :
    ∀ v x, x ∈ allowed Γ plabel outgoing pin v →
      ∀ d, Γ.origin d = v → plabel d ∈ outgoing x := by
  intro v x hx
  exact (Finset.mem_filter.mp hx).2.1

omit [Fintype PV] [Fintype T] in
theorem allowed_card_le (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (v : PV) :
    (allowed Γ plabel outgoing pin v).card ≤ Fintype.card TV :=
  Finset.card_le_univ _

omit [Fintype PV] [Fintype T] in
theorem pinned_card_le (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (v : PV) (y : TV)
    (hp : pin v = some y) : (allowed Γ plabel outgoing pin v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact ((Finset.mem_filter.mp ha).2.2 y hp).trans
    ((Finset.mem_filter.mp hb).2.2 y hp).symm

omit [Fintype PV] [Fintype T] in
/-- A turn at an internal chain vertex restricts its image to the *joint*
carrier. This does not assume independence of consecutive turns. -/
theorem allowed_turn_le (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (v : PV) (a b : PD)
    (ha : Γ.origin a = v) (hb : Γ.origin b = v) :
    (allowed Γ plabel outgoing pin v).card ≤
      Fintype.card {x : TV // plabel a ∈ outgoing x ∧ plabel b ∈ outgoing x} := by
  rw [Fintype.card_subtype]
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    allowed_ports Γ plabel outgoing pin v x hx a ha,
    allowed_ports Γ plabel outgoing pin v x hx b hb⟩

/-- Concrete realization count for one fixed immersed labeling. -/
def realizations (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (bar : T → T)
    (r : Matching (label outgoing) bar) : ℕ :=
  (Finset.univ.filter fun f : VertexMap (allowed Γ plabel outgoing pin) =>
    ∀ d, r.val (dartMap Γ plabel outgoing _ (allowed_ports Γ plabel outgoing pin) f d) =
      dartMap Γ plabel outgoing _ (allowed_ports Γ plabel outgoing pin) f (Γ.reverse d)).card

/-- Finite, exact form of the source fixed-label first moment. `cost v` is a
literal upper bound for carrier size; the matching estimate is proved above. -/
theorem fixed_label_bound (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (bar : T → T)
    (hbar : ∀ t, bar t ≠ t) (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : Dart outgoing // origin outgoing e = v} ≤ d)
    (hsize : ∀ x : Dart outgoing,
      R + (edges Γ).card + 4*d^(2*N+1) ≤
        Nat.card {e : Dart outgoing // label outgoing e = label outgoing x})
    (hΩ : (Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅).Nonempty)
    (cost : PV → ℝ) (hcost : ∀ v, ((allowed Γ plabel outgoing pin v).card : ℝ) ≤ cost v) :
    ((∑ r ∈ Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅, realizations Γ plabel outgoing pin bar r : ℕ) : ℝ) /
      (Matching.conditioned (label := label outgoing) (bar := bar) (origin outgoing) N ∅).card ≤
      (∏ v, cost v) / (R : ℝ)^(edges Γ).card := by
  exact (PatternEmbeddings.expectation_bound Γ plabel outgoing
    (allowed Γ plabel outgoing pin) (allowed_ports Γ plabel outgoing pin)
    bar hbar himm N d R h2 hR hd hsize hΩ).trans
      (div_le_div_of_nonneg_right (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun v _ => hcost v)) (by positivity))

section Typed
open TorsionFreeZeroDivisors.Types
variable (rep : ℕ) (Γ : PortGraph PV PD) (plabel : PD → Letter)
  (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
  (J : Finset PV) (a b : PV → PD)
  (ha : ∀ v ∈ J, Γ.origin (a v) = v) (hb : ∀ v ∈ J, Γ.origin (b v) = v)
  (hab : ∀ v ∈ J, a v ≠ b v)

include himm ha hb hab

end Typed

end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainSubdivision
open scoped Classical BigOperators
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
abbrev Interior := (c : C) × Fin (len c-1)
abbrev Vertex := V ⊕ Interior len
abbrev Edge := (c : C) × Fin (len c)
abbrev Dart := Edge len × Bool

def point (c : C) (k : Fin (len c+1)) : Vertex len (V := V) :=
  if h0 : k.val=0 then .inl (first c) else if h1 : k.val=len c then .inl (last c)
  else .inr ⟨c,⟨k.val-1,by omega⟩⟩

def graph : PortSubdivision.PortGraph (Vertex len (V := V)) (Dart len) where
  origin d := point len first last d.1.1 ⟨d.1.2.val+(if d.2 then 1 else 0),by
    cases d.2 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩
  reverse d := (d.1,!d.2)
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have hh := congrArg Prod.snd h
    cases hb : d.2 <;> simp [hb] at hh

@[simp] theorem reverse (d : Dart len) : (graph len first last).reverse d = (d.1,!d.2) := rfl
@[simp] theorem origin_forward (e : Edge len) :
    (graph len first last).origin (e,false) = point len first last e.1 ⟨e.2.val,by omega⟩ := rfl
@[simp] theorem origin_backward (e : Edge len) :
    (graph len first last).origin (e,true) = point len first last e.1 ⟨e.2.val+1,by omega⟩ := rfl

@[simp] theorem at_zero (c : C) : point len first last c ⟨0,by omega⟩ = .inl (first c) := by
  simp [point]

@[simp] theorem at_interior (c : C) (k : Fin (len c-1)) :
    point len first last c ⟨k.val+1,by omega⟩ = .inr ⟨c,k⟩ := by
  have hk : k.val+1 ≠ len c := by omega
  simp [point,hk]

/-- Outgoing darts at an internal vertex: the preceding edge backwards and
following edge forwards, with no arbitrary choices. -/
def back (v : Interior len) : Dart len := (⟨v.1,⟨v.2.val,by omega⟩⟩,true)
def front (v : Interior len) : Dart len := (⟨v.1,⟨v.2.val+1,by omega⟩⟩,false)

@[simp] theorem back_origin (v : Interior len) :
    (graph len first last).origin (back len v) = .inr v := by
  simpa only [back,origin_backward] using at_interior len first last v.1 v.2
@[simp] theorem front_origin (v : Interior len) :
    (graph len first last).origin (front len v) = .inr v := by
  simpa only [front,origin_forward] using at_interior len first last v.1 v.2

theorem back_ne_front (v : Interior len) : back len v ≠ front len v := by
  intro h
  have hh := congrArg Prod.snd h
  cases hh

variable [Fintype C] [Fintype V]

@[simp] theorem card_edges : Fintype.card (Edge len) = ∑ c, len c := by
  simp [Edge,Fintype.card_sigma]

@[simp] theorem card_darts : Fintype.card (Dart len) = 2*∑ c, len c := by
  simp [Dart,Fintype.card_prod,Nat.mul_comm]

@[simp] theorem card_interiors : Fintype.card (Interior len) = ∑ c, (len c-1) := by
  simp [Interior,Fintype.card_sigma]

end TorsionFreeZeroDivisors.ChainSubdivision

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ListPassages
open scoped Classical BigOperators

lemma rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val+1=n then 0 else i.val+1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [coe_finRotate]
    have h : i=Fin.last n ↔ i.val+1=n+1 := by
      constructor
      · intro he; subst i; rfl
      · intro he; apply Fin.ext; simp only [Fin.val_last]; omega
    simp only [h]

variable {D : Type*} (p : List D) (hp : p ≠ [])

def start : Fin p.length := ⟨0,List.length_pos_iff.mpr hp⟩

def cut (cyclic : Bool) : Option (Fin p.length) :=
  if cyclic then none else some (start p hp)

lemma last_mem (i : Fin p.length) (hi : i.val+1=p.length) :
    p.get i ∈ p.getLast? := by
  have hp : p≠[] := List.length_pos_iff.mp (Nat.zero_lt_of_lt i.isLt)
  rw [List.getLast?_eq_some_getLast hp]
  apply Option.mem_def.mpr
  congr 1
  rw [List.getLast_eq_getElem,List.get_eq_getElem]
  congr 1
  omega

lemma first_mem (i : Fin p.length) (hi : i.val=0) : p.get i ∈ p.head? := by
  cases p with
  | nil => exact Fin.elim0 i
  | cons a p =>
    have he : i=⟨0,by simp⟩ := Fin.ext hi
    subst i
    rfl

/-- The cyclic successor on actual list occurrences pairs exactly the internal
passages, plus the closing passage precisely when the path is cyclic. -/
theorem passage {R : D → D → Prop} (hc : p.IsChain R) (cyclic : Bool)
    (hclose : cyclic=true → ∀ᵉ (x∈p.getLast?) (y∈p.head?),R x y)
    (i : Fin p.length) (hcut : cut p hp cyclic ≠ some (finRotate p.length i)) :
    R (p.get i) (p.get (finRotate p.length i)) := by
  by_cases hi : i.val+1=p.length
  · have hr : (finRotate p.length i).val=0 := by rw [rotate_val,if_pos hi]
    have hcyc : cyclic=true := by
      cases cyclic
      · exfalso
        apply hcut
        apply congrArg some
        apply Fin.ext
        exact hr.symm
      · rfl
    exact hclose hcyc _ (last_mem p i hi) _ (first_mem p _ hr)
  · have hir : i.val+1<p.length := by omega
    have hr : (finRotate p.length i).val=i.val+1 := by rw [rotate_val,if_neg hi]
    have h := (List.isChain_iff_getElem.mp hc) i.val hir
    simpa only [List.get_eq_getElem,hr] using h

end TorsionFreeZeroDivisors.ListPassages
namespace TorsionFreeZeroDivisors.ChainPathTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open WeightedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "w" => word Γ mark h2

end TorsionFreeZeroDivisors.ChainPathTransport
namespace TorsionFreeZeroDivisors.ListStageExponents
open scoped Classical BigOperators
open PortSubdivision WeightedMoore StageSubgraphs
variable {V D I : Type*} [Fintype V] [Fintype D] [Fintype I]
    (Γ : PortGraph V D) (p : I → List D) (hp : ∀ i,p i ≠ [])
    (cyclic : I → Bool)
    (hc : ∀ i,(p i).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(p i).getLast?) (y∈(p i).head?),
      PortWalk.step Γ.origin Γ.reverse x y)

abbrev edge (i : I) : Fin (p i).length → D := (p i).get
abbrev mult : D → ℕ := multiplicity Γ (edge p)

omit [Fintype D] in
theorem cut_count : (∑ i,if (ListPassages.cut (p i) (hp i) (cyclic i)).isSome then 1 else 0 : ℕ) =
    Fintype.card {i : I // cyclic i=false} := by
  rw [Fintype.card_subtype,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases cyclic i <;> simp [ListPassages.cut]

include hp hc hclose in
/-- The exact signed stage exponent of literal immersed paths, including a
root saving for each noncyclic interval only at the first stage. -/
theorem exponent_nonpos (M : ℕ) (hM : 0<M) (hm : ∀ d,mult Γ p d ≤ M) :
    (∑ j : Fin M, ((Fintype.card (ActiveV Γ (mult Γ p) j.val):ℤ)-
      (edges (stage Γ (mult Γ p) (multiplicity_reverse Γ (edge p)) j.val)).card-
      if j.val=0 then Fintype.card {i : I // cyclic i=false} else 0)) ≤ 0 := by
  have hv : ∀ i (e : Fin (p i).length),
      ListPassages.cut (p i) (hp i) (cyclic i) ≠ some (finRotate (p i).length e) →
      Γ.origin (edge p i (finRotate (p i).length e))=Γ.origin (Γ.reverse (edge p i e)) := by
    intro i e he
    exact (ListPassages.passage (p i) (hp i) (hc i) (cyclic i) (hclose i) e he).1.symm
  have hr : ∀ i (e : Fin (p i).length),
      ListPassages.cut (p i) (hp i) (cyclic i) ≠ some (finRotate (p i).length e) →
      edge p i (finRotate (p i).length e)≠Γ.reverse (edge p i e) := by
    intro i e he
    exact (ListPassages.passage (p i) (hp i) (hc i) (cyclic i) (hclose i) e he).2
  have h := family_exponent_nonpos Γ (edge p) (fun i => finRotate (p i).length)
    (fun i => ListPassages.cut (p i) (hp i) (cyclic i)) hv hr M hM hm
  rw [cut_count] at h
  exact h

end TorsionFreeZeroDivisors.ListStageExponents

/-! A choice of one direction for each unoriented edge of a finite port graph.
The reversal has no fixed points. No graph is assumed bipartite or loop-free. -/
namespace TorsionFreeZeroDivisors.InvolutionOrientation
open scoped Classical BigOperators
variable {D : Type*} [Fintype D] (σ : D → D)

variable (hσ : Function.Involutive σ) (hne : ∀d,σ d≠d)

include hσ hne

@[simp] lemma equiv_false (c : Representative σ) : equiv σ hσ hne (c,false) = c.val := rfl
@[simp] lemma equiv_true (c : Representative σ) : equiv σ hσ hne (c,true) = σ c.val := rfl

end TorsionFreeZeroDivisors.InvolutionOrientation
namespace TorsionFreeZeroDivisors.ChainIsomorphism
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => InvolutionOrientation.Representative (PortGraph.reverse (suppressed Γ mark h2))
local notation "len" => chainLength Γ mark h2

abbrev repLength (c : R) := len c.val

def first (c : R) : Mark mark :=
  ⟨Γ.origin c.val.val,(turn_fixed_iff Γ.origin mark h2 _).mp c.val.property⟩
def last (c : R) : Mark mark :=
  ⟨Γ.origin ((S).reverse c.val).val,(turn_fixed_iff Γ.origin mark h2 _).mp ((S).reverse c.val).property⟩

local notation "P" => ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2)

def dartMap (d : ChainSubdivision.Dart (repLength Γ mark h2)) : D :=
  if d.2 then Γ.reverse (F^[d.1.2.val] d.1.1.val.val) else F^[d.1.2.val] d.1.1.val.val

lemma forward_mem (c : R) (i : Fin (len c.val)) :
    F^[i.val] c.val.val ∈ ChainPaths.word Γ mark h2 c.val :=
  (ChainPaths.mem_word_iff Γ mark h2 _ _).mpr ⟨i,rfl⟩

lemma dart_mem (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    dartMap Γ mark h2 d ∈ ChainPaths.word Γ mark h2
      (InvolutionOrientation.orient (S).reverse (d.1.1,d.2)) := by
  cases hb : d.2
  · simpa only [dartMap,InvolutionOrientation.orient,hb,Bool.false_eq_true,ite_false] using
      forward_mem Γ mark h2 d.1.1 d.1.2
  · simpa only [dartMap,InvolutionOrientation.orient,hb,ite_true] using
      ChainPaths.reverse_mem_word Γ mark h2 _ _ (forward_mem Γ mark h2 d.1.1 d.1.2)

lemma same_word {a b : B} {x : D} (ha : x∈ChainPaths.word Γ mark h2 a)
    (hb : x∈ChainPaths.word Γ mark h2 b) : a=b := by
  by_contra h
  exact ChainPaths.words_disjoint Γ mark h2 h ha hb

lemma dartMap_injective : Injective (dartMap Γ mark h2) := by
  rintro ⟨⟨a,i⟩,u⟩ ⟨⟨b,j⟩,v⟩ he
  have hw := same_word Γ mark h2 (dart_mem Γ mark h2 ((⟨a,i⟩),u))
    (he.symm ▸ dart_mem Γ mark h2 ((⟨b,j⟩),v))
  have hab := InvolutionOrientation.orient_injective (S).reverse (S).reverse_reverse (S).reverse_ne hw
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hab
  have hi : F^[i.val] a.val.val=F^[j.val] a.val.val := by
    cases u
    · exact he
    · exact Γ.reverse_reverse.injective he
  have hij := chain_dart_injective Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    (a₁ := ⟨a.val,i⟩) (a₂ := ⟨a.val,j⟩) hi
  have hij' : i=j := Fin.ext (congrArg (fun z => z.2.val) hij)
  cases hij'
  rfl

lemma dartMap_surjective (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : Surjective (dartMap Γ mark h2) := by
  intro x
  rcases hcovered x with ⟨b,i,hi⟩
  rcases InvolutionOrientation.chosen_or_reverse (S).reverse
    (S).reverse_reverse (S).reverse_ne b with hb|hb
  · exact ⟨(⟨⟨b,hb⟩,i⟩,false),hi⟩
  · have hx : x∈ChainPaths.word Γ mark h2 b :=
      (ChainPaths.mem_word_iff Γ mark h2 _ _).mpr ⟨i,hi⟩
    have hr := ChainPaths.reverse_mem_word Γ mark h2 b x hx
    rcases (ChainPaths.mem_word_iff Γ mark h2 _ _).mp hr with ⟨j,hj⟩
    refine ⟨(⟨⟨(S).reverse b,hb⟩,j⟩,true),?_⟩
    exact (congrArg Γ.reverse hj).trans (Γ.reverse_reverse x)

def dartEquiv (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : ChainSubdivision.Dart (repLength Γ mark h2) ≃ D :=
  Equiv.ofBijective (dartMap Γ mark h2)
    ⟨dartMap_injective Γ mark h2,dartMap_surjective Γ mark h2 hcovered⟩

lemma dartMap_reverse (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    dartMap Γ mark h2 ((P).reverse d)=Γ.reverse (dartMap Γ mark h2 d) := by
  cases hb : d.2 <;> simp only [ChainSubdivision.reverse,dartMap,hb,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,ite_false,ite_true]
  exact (Γ.reverse_reverse _).symm

def vertexMap : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) → V
  | .inl v => v.val
  | .inr ⟨c,i⟩ => Γ.origin (F^[i.val+1] c.val.val)

lemma internal_unmarked (v : ChainSubdivision.Interior (repLength Γ mark h2)) :
    ¬mark (vertexMap Γ mark h2 (.inr v)) := by
  intro hh
  have hf := (turn_fixed_iff Γ.origin mark h2 _).mpr hh
  have hi : v.2.val+1 < len v.1.val := by have h:=v.2.isLt; dsimp only [repLength] at h; omega
  exact no_internal_mark Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    v.1.val.val v.1.val.property (by omega : 0<v.2.val+1) hi hf

lemma origin_map (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    vertexMap Γ mark h2 ((P).origin d) = Γ.origin (dartMap Γ mark h2 d) := by
  rcases d with ⟨⟨c,i⟩,b⟩
  cases b
  · rw [ChainSubdivision.origin_forward]
    by_cases hz : i.val=0
    · simp only [ChainSubdivision.point,Fin.val_mk,hz,dif_pos,vertexMap,first,dartMap,
        Bool.false_eq_true,ite_false]
      rfl
    · have hl : i.val≠repLength Γ mark h2 c := Nat.ne_of_lt i.isLt
      simp only [ChainSubdivision.point,hz,hl,vertexMap,dartMap,
        Bool.false_eq_true,ite_false]
      change Γ.origin (F^[i.val-1+1] c.val.val) = Γ.origin (F^[i.val] c.val.val)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hz)]
  · rw [ChainSubdivision.origin_backward]
    have hz : i.val+1≠0 := by omega
    by_cases hl : i.val+1=repLength Γ mark h2 c
    · have hp : repLength Γ mark h2 c≠0 := Nat.ne_of_gt (chainLength_pos Γ mark h2 c.val)
      simp only [ChainSubdivision.point,Fin.val_mk,hl,hp,dif_pos,vertexMap,last,
        dartMap,ite_true]
      have hi : i.val=len c.val-1 := by change i.val+1=len c.val at hl; omega
      have he := chain_last Γ mark h2 c.val
      rw [last_iterChain] at he
      change Γ.origin ((S).reverse c.val).val = Γ.origin (Γ.reverse (F^[i.val] c.val.val))
      rw [hi,he]
    · simp only [ChainSubdivision.point,hz,hl,vertexMap,dartMap,ite_true]
      change Γ.origin (F^[i.val+1-1+1] c.val.val) = Γ.origin (Γ.reverse (F^[i.val] c.val.val))
      rw [Nat.add_sub_cancel,iterate_succ_apply']
      exact turn_origin Γ.origin mark h2 _

lemma original_two_ports (v : ChainSubdivision.Interior (repLength Γ mark h2))
    (d : D) (hd : Γ.origin d=vertexMap Γ mark h2 (.inr v)) :
    d=dartMap Γ mark h2 (ChainSubdivision.front (repLength Γ mark h2) v) ∨
    d=dartMap Γ mark h2 (ChainSubdivision.back (repLength Γ mark h2) v) := by
  let a := ChainSubdivision.front (repLength Γ mark h2) v
  let b := ChainSubdivision.back (repLength Γ mark h2) v
  have ha : Γ.origin (dartMap Γ mark h2 a)=vertexMap Γ mark h2 (.inr v) := by
    rw [←origin_map,ChainSubdivision.front_origin]
  have hb : Γ.origin (dartMap Γ mark h2 b)=vertexMap Γ mark h2 (.inr v) := by
    rw [←origin_map,ChainSubdivision.back_origin]
  by_cases hda : d=dartMap Γ mark h2 a
  · exact Or.inl hda
  · right
    have hba : dartMap Γ mark h2 b≠dartMap Γ mark h2 a := by
      intro hh
      exact ChainSubdivision.back_ne_front _ v (dartMap_injective Γ mark h2 hh)
    exact ((unique_other Γ.origin (dartMap Γ mark h2 a)
      (h2 _ (ha ▸ internal_unmarked Γ mark h2 v))).unique
        ⟨hd.trans ha.symm,hda⟩ ⟨hb.trans ha.symm,hba⟩)

lemma vertexMap_injective : Injective (vertexMap Γ mark h2) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext he)
    | inr b => exact (internal_unmarked Γ mark h2 b (he ▸ a.property)).elim
  | inr a =>
    cases b with
    | inl b => exact (internal_unmarked Γ mark h2 a (he.symm ▸ b.property)).elim
    | inr b =>
      have hb : Γ.origin (dartMap Γ mark h2 (ChainSubdivision.front (repLength Γ mark h2) b)) =
          vertexMap Γ mark h2 (.inr a) := by
        rw [←origin_map,ChainSubdivision.front_origin,he]
      rcases original_two_ports Γ mark h2 a _ hb with h|h
      · have hh := dartMap_injective Γ mark h2 h
        have h' := congrArg (fun d => (P).origin d) hh
        simpa only [ChainSubdivision.front_origin] using h'.symm
      · have hh := dartMap_injective Γ mark h2 h
        have h' := congrArg Prod.snd hh
        cases h'

lemma vertexMap_surjective (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : Surjective (vertexMap Γ mark h2) := by
  intro v
  by_cases hv : mark v
  · exact ⟨.inl ⟨v,hv⟩,rfl⟩
  · have hp : (out Γ.origin v).Nonempty := Finset.card_pos.mp (by rw [h2 v hv]; decide)
    obtain ⟨d,hd⟩ := hp
    obtain ⟨a,ha⟩ := dartMap_surjective Γ mark h2 hcovered d
    refine ⟨(P).origin a,?_⟩
    rw [origin_map,ha]
    exact (mem_out Γ.origin v d).mp hd

def vertexEquiv (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) ≃ V :=
  Equiv.ofBijective (vertexMap Γ mark h2)
    ⟨vertexMap_injective Γ mark h2,vertexMap_surjective Γ mark h2 hcovered⟩

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainIsomorphism

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open ComparedBlocks
variable {P T U C : Type*} {lp : P → ℕ} {lt : T → ℕ}

def positionEquiv (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) :
    Position lu ≃ Position lt :=
  Equiv.sigmaCongr r (fun u => (Equiv.refl ℤ).subtypeEquiv (by
    intro q
    change q∈BlockAlignment.positions 0 (lu u) ↔ q∈BlockAlignment.positions 0 (lt (r u))
    rw [hlen]))

lemma positionEquiv_source (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) (x : Position lu) :
    (positionEquiv r lu hlen x).1=r x.1 := rfl

lemma positionEquiv_coordinate (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) (x : Position lu) :
    (positionEquiv r lu hlen x).2.val=x.2.val := rfl

namespace Chunking
/-- Re-enumerating occurrence chunks does not change their geometric partition. -/
def reindex (K : Chunking lp lt) (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) : Chunking lp lu where
  equiv := (positionEquiv r lu hlen).trans K.equiv
  path u := K.path (r u)
  reverse u := K.reverse (r u)
  offset u := K.offset (r u)
  source x := K.source (positionEquiv r lu hlen x)
  coordinate x := K.coordinate (positionEquiv r lu hlen x)
end Chunking

variable [Fintype T] (color : T → C)

/-- Exact color-fibre enumeration, identifying the literal path traversals
with the multiplicity-indexed traversal type used in every stage estimate. -/
def enumeration : ((c : C) × Fin (multiplicity color c)) ≃ T :=
  (Equiv.sigmaCongrRight (fun c => (Fintype.equivFin {t // color t=c}).symm)).trans
    (Equiv.sigmaFiberEquiv color)

lemma enumeration_color (o : (c : C) × Fin (multiplicity color c)) : color (enumeration color o)=o.1 :=
  ((Fintype.equivFin {t // color t=o.1}).symm o.2).property

lemma enumeration_length (len : C → ℕ) (hl : ∀ t,lt t=len (color t))
    (o : (c : C) × Fin (multiplicity color c)) : len o.1=lt (enumeration color o) := by
  rw [hl (enumeration color o),enumeration_color color o]

/-- The complete finite reindexing into underlying chain and occurrence number. -/
def repeated (K : Chunking lp lt) (len : C → ℕ) (hl : ∀ t,lt t=len (color t)) :
    Chunking lp (fun o : (c : C) × Fin (multiplicity color c) => len o.1) :=
  K.reindex (enumeration color) _ (enumeration_length color len hl)

end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.ListChunkCoordinates
open scoped Classical BigOperators
open FiniteChunking
variable {A D : Type*} (ds : List A) (word : A → List D)

lemma start_eq (i : Fin ds.length) :
    start (lengths ds word) i = ((ds.take i.val).flatMap word).length := by
  rw [List.length_flatMap,List.map_take,← ofFn_lengths,List.sum_take_ofFn]
  simp only [start,before,Fin.lt_def]

/-- Literal indexing through a list concatenation, including repeated chunks. -/
lemma get_flatMap (i : Fin ds.length) (q : Fin (lengths ds word i)) :
    (ds.flatMap word)[start (lengths ds word) i+q.val]? = some ((word (ds.get i)).get q) := by
  rw [start_eq]
  have hdec : ds.take i.val ++ ds.get i :: ds.drop (i.val+1)=ds := by
    simpa only [List.drop_eq_getElem_cons i.isLt,List.get_eq_getElem] using List.take_append_drop i.val ds
  have hflat := congrArg (List.flatMap word) hdec
  simp only [List.flatMap_append,List.flatMap_cons] at hflat
  calc
    _ = (((ds.take i.val).flatMap word) ++
        (word (ds.get i) ++ (ds.drop (i.val+1)).flatMap word))[
          ((ds.take i.val).flatMap word).length+q.val]? := by rw [hflat]
    _ = (word (ds.get i) ++ (ds.drop (i.val+1)).flatMap word)[q.val]? := by
      rw [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
    _ = some ((word (ds.get i)).get q) := by
      rw [List.getElem?_append_left q.isLt,List.getElem?_eq_getElem q.isLt]
      rfl

end TorsionFreeZeroDivisors.ListChunkCoordinates

namespace TorsionFreeZeroDivisors.ChainChunkTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChunkComparisons FiniteChunking ComparedBlocks
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "len" => chainLength Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "w" => word Γ mark h2

def reversed (b : B) : Bool := ((orientation Γ mark h2).symm b).2

lemma oriented (b : B) : b=if reversed Γ mark h2 b then (S).reverse (representative Γ mark h2 b).val
    else (representative Γ mark h2 b).val := (orientation Γ mark h2).apply_symm_apply b |>.symm

lemma oriented_length (b : B) : len b=len (representative Γ mark h2 b).val := by
  have h := oriented Γ mark h2 b
  conv_lhs => rw [h]
  split_ifs <;> simp only [chainLength_reverse]

lemma word_get (b : B) (i : ℕ) (hi : i < len b) : (w b)[i]?=some (F^[i] b.val) := by
  simp [word_eq_range,hi]

lemma reverse_iter (b : B) (i : ℕ) (hi : i < len b) :
    F^[len b-i-1] ((S).reverse b).val=Γ.reverse (F^[i] b.val) := by
  let k := len b
  have hf := endpoint_reverse Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (x:=b) (i:=k-i) (by change k-i ≤ k; omega)
  have he : k-(k-i)=i := by dsimp [k]; omega
  have hs : k-i=(k-i-1)+1 := by dsimp [k]; omega
  change F^[k-i] ((S).reverse b).val = τ (F^[k-(k-i)] b.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (Γ.reverse (F^[k-i-1] ((S).reverse b).val))) = τ (τ (F^[i] b.val)) at h
  rw [turn_involutive Γ.origin mark h2,turn_involutive Γ.origin mark h2] at h
  have hh := congrArg Γ.reverse h
  rwa [Γ.reverse_reverse] at hh

lemma listDart (b : B) (q : ℤ) (hq : q∈BlockAlignment.positions 0 (len b)) :
    (w b)[(localIndex (reversed Γ mark h2 b) (len b) q).toNat]? =
      some (if reversed Γ mark h2 b then Γ.reverse (F^[q.toNat] (representative Γ mark h2 b).val.val)
        else F^[q.toNat] (representative Γ mark h2 b).val.val) := by
  have hz : 0 ≤ q ∧ q < len b := by simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using hq
  have hqcast : (q.toNat : ℤ)=q := Int.toNat_of_nonneg hz.1
  have hqn : q.toNat < len b := by omega
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simp only [hr,Bool.false_eq_true,ite_false] at h ⊢
    simp only [localIndex,BlockAlignment.affine,Bool.false_eq_true,ite_false,add_zero]
    rw [word_get Γ mark h2 b q.toNat hqn,show b.val=(representative Γ mark h2 b).val.val from congrArg Subtype.val h]
  · simp only [hr,ite_true] at h ⊢
    have he : (localIndex true (len b) q).toNat=len b-q.toNat-1 := by
      simp only [localIndex,BlockAlignment.affine,ite_true]
      omega
    have hi : len b-q.toNat-1 < len b := by omega
    rw [he,word_get Γ mark h2 b _ hi]
    apply congrArg some
    rw [oriented_length Γ mark h2 b,show b.val=((S).reverse (representative Γ mark h2 b).val).val from congrArg Subtype.val h]
    apply reverse_iter
    rwa [←oriented_length Γ mark h2 b]

variable {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

def chunkReverse (p : P) (i : Fin (chunks Γ mark h2 paths p)) : Bool := reversed Γ mark h2 ((paths p).get i)

def splitChunks := FiniteChunking.chunking (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) (chunkReverse Γ mark h2 paths)

omit [Fintype P] in
lemma chunkLength_eq (t : Traversal (chunks Γ mark h2 paths)) :
    traversalLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) t=repLength Γ mark h2 (color Γ mark h2 paths t) := by
  exact (word_length Γ mark h2 _).trans (oriented_length Γ mark h2 _)

/-- The original path's actual dart at the signed chunk image. -/
lemma chunk_dart (x : Position (traversalLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) :
    ((paths x.1.1).flatMap w)[((splitChunks Γ mark h2 paths).equiv x).2.val.toNat]? =
      some (if (splitChunks Γ mark h2 paths).reverse x.1 then
        Γ.reverse (F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val)
        else F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val) := by
  let b := (paths x.1.1).get x.1.2
  let q := localIndex (reversed Γ mark h2 b) (len b) x.2.val
  have hlen : chunkLength Γ mark h2 paths x.1.1 x.1.2=len b := word_length Γ mark h2 b
  have hq : x.2.val∈BlockAlignment.positions 0 (len b) := by
    have h := x.2.property
    change x.2.val∈BlockAlignment.positions 0 (chunkLength Γ mark h2 paths x.1.1 x.1.2) at h
    rwa [hlen] at h
  have hqb := local_bounds (reversed Γ mark h2 b) (len b) hq
  have hn : q.toNat < chunkLength Γ mark h2 paths x.1.1 x.1.2 := by
    rw [hlen]
    dsimp [q]
    omega
  have hflat := ListChunkCoordinates.get_flatMap (paths x.1.1) w x.1.2 ⟨q.toNat,hn⟩
  have him : ((splitChunks Γ mark h2 paths).equiv x).2.val.toNat=
      start (chunkLength Γ mark h2 paths x.1.1) x.1.2+q.toNat := by
    change (FiniteChunking.image _ _ _ x).2.val.toNat = _
    rw [FiniteChunking.image_val]
    change ((start (chunkLength Γ mark h2 paths x.1.1) x.1.2:ℤ)+
      localIndex (reversed Γ mark h2 b) (chunkLength Γ mark h2 paths x.1.1 x.1.2) x.2.val).toNat = _
    rw [hlen]
    omega
  change ((paths x.1.1).flatMap w)[start (chunkLength Γ mark h2 paths x.1.1) x.1.2+q.toNat]? =
    some ((w b).get ⟨q.toNat,hn⟩) at hflat
  rw [him,hflat]
  have hd := listDart Γ mark h2 b x.2.val hq
  rw [List.getElem?_eq_getElem hn] at hd
  exact hd

omit [Fintype P] in
lemma originalDart_get (x : Position (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) :
    ((paths x.1).flatMap w)[x.2.val.toNat]?=some (originalDart Γ mark h2 paths x) :=
  List.getElem?_eq_getElem _

lemma chunk_original (x : Position (traversalLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) :
    originalDart Γ mark h2 paths ((splitChunks Γ mark h2 paths).equiv x)=
      if (splitChunks Γ mark h2 paths).reverse x.1 then
        Γ.reverse (F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val)
      else F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val := by
  apply Option.some.inj
  rw [←originalDart_get]
  exact chunk_dart Γ mark h2 paths x

def repeatedChunks := ChunkComparisons.repeated (color Γ mark h2 paths)
  (splitChunks Γ mark h2 paths) (repLength Γ mark h2) (chunkLength_eq Γ mark h2 paths)

lemma repeated_original (x : Position (fun o : (c : R) × Fin (multiplicity (color Γ mark h2 paths) c) => repLength Γ mark h2 o.1)) :
    originalDart Γ mark h2 paths ((repeatedChunks Γ mark h2 paths).equiv x)=
      if (repeatedChunks Γ mark h2 paths).reverse x.1 then
        Γ.reverse (F^[x.2.val.toNat] x.1.1.val.val)
      else F^[x.2.val.toNat] x.1.1.val.val := by
  unfold repeatedChunks ChunkComparisons.repeated Chunking.reindex
  change originalDart Γ mark h2 paths ((splitChunks Γ mark h2 paths).equiv _)=_
  rw [chunk_original]
  simp only [positionEquiv_source,positionEquiv_coordinate,enumeration_color]

omit [Fintype D] in
lemma signed_eq_or_reverse (r s : Bool) (d : D) :
    (if r then Γ.reverse d else d) = (if s then Γ.reverse d else d) ∨
    (if r then Γ.reverse d else d) = Γ.reverse (if s then Γ.reverse d else d) := by
  cases r <;> cases s <;> simp

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

/-- Reduction survives signed normalization: neither orientation of an actual
paired undirected edge can become the same chain-coordinate position. -/
lemma normalized_reduced
    (hred : ∀ x e,cmp.side x=some e →
      originalDart Γ mark h2 paths x≠originalDart Γ mark h2 paths (cmp.pairing.partner x) ∧
      originalDart Γ mark h2 paths x≠Γ.reverse (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ∀ x a,((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).side x=some a →
      (x.1.1,x.2.val)≠
      ((((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).pairing.partner x).1.1,
       (((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).pairing.partner x).2.val) := by
  intro x a ha heq
  let K := repeatedChunks Γ mark h2 paths
  have he := ((K.side_iff cmp x a.1 a.2.1 a.2.2).mp ha).1
  have hbad := hred (K.equiv x) a.1 he
  rw [←K.partner_image, repeated_original, repeated_original] at hbad
  have hd : F^[x.2.val.toNat] x.1.1.val.val =
      F^[((K.pairing cmp).partner x).2.val.toNat] ((K.pairing cmp).partner x).1.1.val.val := by
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    change x.1.1=((K.pairing cmp).partner x).1.1 at h1
    change x.2.val=((K.pairing cmp).partner x).2.val at h2
    rw [h1,h2]
  rw [hd] at hbad
  exact (signed_eq_or_reverse Γ (K.reverse x.1) (K.reverse ((K.pairing cmp).partner x).1) _).elim hbad.1 hbad.2

/-- Actual graph labels, including reversal, induce precisely the literal
compatibility constraints used by the repeated-block entropy estimates. -/
lemma normalized_compatible {A : Type*} (bar : A → A) (hb : Function.Involutive bar)
    (label : D → A) (hl : ∀ d,label (Γ.reverse d)=bar (label d))
    (hc : ∀ x e,cmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if cmp.reverse e then bar (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ∀ x a,((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).side x=some a →
      label (F^[x.2.val.toNat] x.1.1.val.val)=
      if ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).reverse a then
        bar (label (F^[(((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).2.val.toNat]
          (((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).1.1.val.val))
      else label (F^[(((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).2.val.toNat]
          (((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).1.1.val.val) := by
  apply (repeatedChunks Γ mark h2 paths).compatible cmp lo hi hlo hhi bar hb
    (fun x => label (originalDart Γ mark h2 paths x))
    (fun x => label (F^[x.2.val.toNat] x.1.1.val.val)) _ hc
  intro x
  rw [repeated_original]
  split_ifs <;> simp only [hl]

/-- A step strictly inside a suppressed chain is an actual reduced graph
passage, with both outgoing ports at precisely the same original vertex. -/
lemma internal_step (d : B) (i : ℕ) (hi : i+1 < len d) :
    Γ.origin (F^[i+1] d.val)=Γ.origin (Γ.reverse (F^[i] d.val)) ∧
      F^[i+1] d.val≠Γ.reverse (F^[i] d.val) := by
  constructor
  · rw [iterate_succ_apply']
    exact turn_origin Γ.origin mark h2 _
  · intro he
    have hn := ChainSuppression.no_internal_mark Γ.reverse τ Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d.val d.property (by omega : 0 < i+1) hi
    apply hn
    conv_lhs => rw [iterate_succ_apply']
    change τ (τ (Γ.reverse (F^[i] d.val)))=F^[i+1] d.val
    rw [turn_involutive Γ.origin mark h2,he]

/-- Immersion of the literal labelled graph gives the reduced signed chain
words required by every reflection and squared-word argument. -/
lemma normalized_immersed {A : Type*} (bar : A → A) (label : D → A)
    (hl : ∀ d,label (Γ.reverse d)=bar (label d))
    (hinj : ∀ d e,Γ.origin d=Γ.origin e → label d=label e → d=e)
    (c : R) (q : ℤ) (hq : 0≤q) (hq' : q+1<repLength Γ mark h2 c) :
    label (F^[(q+1).toNat] c.val.val)≠bar (label (F^[q.toNat] c.val.val)) := by
  have hn : (q+1).toNat=q.toNat+1 := by omega
  have hi : q.toNat+1<len c.val := by change q+1<len c.val at hq'; omega
  have hs := internal_step Γ mark h2 c.val q.toNat hi
  intro he
  rw [hn,←hl] at he
  exact hs.2 (hinj _ _ hs.1 he)

end TorsionFreeZeroDivisors.ChainChunkTransport

namespace TorsionFreeZeroDivisors.ChainMultiplicity
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2

lemma representative_val (c : R) : representative Γ mark h2 c.val=c := by
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c,false))).1=c
  rw [Equiv.symm_apply_apply]

lemma reverse_oriented (b : B) :
    (S).reverse b=(orientation Γ mark h2) (representative Γ mark h2 b,!(reversed Γ mark h2 b)) := by
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simp only [hr,Bool.false_eq_true,ite_false] at h
    change (S).reverse b=(S).reverse (representative Γ mark h2 b).val
    exact congrArg (S).reverse h
  · simp only [hr,ite_true] at h
    change (S).reverse b=(representative Γ mark h2 b).val
    calc
      _ = (S).reverse ((S).reverse (representative Γ mark h2 b).val) := congrArg (S).reverse h
      _ = _ := (S).reverse_reverse _

lemma representative_reverse (b : B) : representative Γ mark h2 ((S).reverse b)=representative Γ mark h2 b := by
  rw [reverse_oriented]
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) _)).1=_
  rw [Equiv.symm_apply_apply]

lemma unsigned (b : B) :
    (if reversed Γ mark h2 b then (S).reverse b else b)=(representative Γ mark h2 b).val := by
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simpa only [hr,Bool.false_eq_true,ite_false] using h
  · simp only [hr,ite_true] at h ⊢
    calc
      _ = (S).reverse ((S).reverse (representative Γ mark h2 b).val) := congrArg (S).reverse h
      _ = _ := (S).reverse_reverse _

lemma signed_representative (b : B) (r : Bool) :
    representative Γ mark h2 (if r then (S).reverse b else b)=representative Γ mark h2 b := by
  cases r <;> simp only [Bool.false_eq_true,ite_false,ite_true,representative_reverse]

lemma sign_injective (b : B) : Function.Injective (fun r : Bool => if r then (S).reverse b else b) := by
  intro r t h
  cases r <;> cases t <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · exact ((S).reverse_ne b h.symm).elim
  · exact ((S).reverse_ne b h).elim

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

local notation "col" => color Γ mark h2 paths
local notation "tp" => Traversal (chunks Γ mark h2 paths)
local notation "e" => ListStageExponents.edge paths

/-- The incidence fibre used in the Euler-exponent proof is the exact colour
fibre used in the chain/block first moment. Both chain orientations count once. -/
def incidenceEquiv (c : R) :
    {o : (p : P) × (Fin (paths p).length × Bool) // PathIncidences.familyPort (S).reverse e o=c.val} ≃
      {t : tp // col t=c} where
  toFun o := ⟨⟨o.val.1,o.val.2.1⟩,by
    have h := congrArg (representative Γ mark h2) o.property
    change representative Γ mark h2 (if o.val.2.2 then (S).reverse ((paths o.val.1).get o.val.2.1)
      else (paths o.val.1).get o.val.2.1)=representative Γ mark h2 c.val at h
    rw [signed_representative,representative_val] at h
    exact h⟩
  invFun t := ⟨⟨t.val.1,t.val.2,reversed Γ mark h2 ((paths t.val.1).get t.val.2)⟩,by
    change (if reversed Γ mark h2 ((paths t.val.1).get t.val.2) then
      (S).reverse ((paths t.val.1).get t.val.2) else (paths t.val.1).get t.val.2)=c.val
    rw [unsigned]
    exact congrArg Subtype.val t.property⟩
  left_inv := by
    rintro ⟨⟨p,i,r⟩,ho⟩
    apply Subtype.ext
    change (⟨p,i,reversed Γ mark h2 ((paths p).get i)⟩ : (p : P) × (Fin (paths p).length × Bool))=⟨p,i,r⟩
    have hr : reversed Γ mark h2 ((paths p).get i)=r := by
      apply sign_injective Γ mark h2 ((paths p).get i)
      dsimp only
      rw [unsigned]
      have h := congrArg (representative Γ mark h2) ho
      change representative Γ mark h2 (if r then (S).reverse ((paths p).get i)
        else (paths p).get i)=representative Γ mark h2 c.val at h
      rw [signed_representative,representative_val] at h
      rw [h]
      exact ho.symm
    rw [hr]
  right_inv _ := rfl

lemma multiplicity_eq (c : R) :
    StageSubgraphs.multiplicity (S) e c.val=ChunkComparisons.multiplicity col c := by
  classical
  unfold StageSubgraphs.multiplicity IncidenceStages.Passages.multiplicity ChunkComparisons.multiplicity
  simp only [Fintype.card_eq_nat_card]
  exact Nat.card_congr (incidenceEquiv Γ mark h2 paths c)

lemma multiplicity_at (b : B) :
    StageSubgraphs.multiplicity (S) e b=
      ChunkComparisons.multiplicity col (representative Γ mark h2 b) := by
  have h := oriented Γ mark h2 b
  conv_lhs => rw [h]
  split_ifs
  · rw [StageSubgraphs.multiplicity_reverse,multiplicity_eq]
  · exact multiplicity_eq Γ mark h2 paths _

end TorsionFreeZeroDivisors.ChainMultiplicity

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainActiveStages
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths
local notation "e" => ListStageExponents.edge paths
local notation "m" => StageSubgraphs.multiplicity (S) e
abbrev ActiveChain (j : ℕ) := {c : R // j < ChunkComparisons.multiplicity col c}
local notation "A" => ActiveChain Γ mark h2 paths

/-- Literal active chain orientations, with no padding by inactive chains. -/
def activeOrientation (j : ℕ) : ActiveD m j ≃ A j × Bool where
  toFun d := (⟨representative Γ mark h2 d.val,by
    rw [←multiplicity_at Γ mark h2 paths]; exact d.property⟩,reversed Γ mark h2 d.val)
  invFun c := ⟨orientation Γ mark h2 (c.1.val,c.2),by
    rw [multiplicity_at Γ mark h2 paths]
    change j < ChunkComparisons.multiplicity col (((orientation Γ mark h2).symm ((orientation Γ mark h2) (c.1.val,c.2))).1)
    rw [Equiv.symm_apply_apply]
    exact c.1.property⟩
  left_inv d := by
    apply Subtype.ext
    exact (orientation Γ mark h2).apply_symm_apply d.val
  right_inv c := by
    apply Prod.ext
    · apply Subtype.ext
      change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c.1.val,c.2))).1=c.1.val
      rw [Equiv.symm_apply_apply]
    · change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c.1.val,c.2))).2=c.2
      rw [Equiv.symm_apply_apply]

variable [Fintype V]

omit [Fintype V] in
lemma edges_card (j : ℕ) :
    (edges (stage (S) m (multiplicity_reverse (S) e) j)).card=Fintype.card (A j) := by
  have ha := Fintype.card_congr (activeOrientation Γ mark h2 paths j)
  rw [Fintype.card_prod,Fintype.card_bool] at ha
  have he := two_edges (stage (S) m (multiplicity_reverse (S) e) j)
  omega

def first (j : ℕ) (c : A j) : ActiveV (S) m j :=
  ⟨ChainIsomorphism.first Γ mark h2 c.val,c.val.val,rfl,by
    rw [multiplicity_eq Γ mark h2 paths]; exact c.property⟩

def last (j : ℕ) (c : A j) : ActiveV (S) m j :=
  ⟨ChainIsomorphism.last Γ mark h2 c.val,(S).reverse c.val.val,rfl,by
    rw [multiplicity_reverse,multiplicity_eq Γ mark h2 paths]; exact c.property⟩

/-- The signed exponent counted by the chain expectation is exactly the one
bounded by immersed path incidence, including the first-stage root saving. -/
theorem exponent_nonpos (hp : ∀ i,paths i≠[]) (cyclic : P → Bool)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step (S).origin (S).reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (S).origin (S).reverse x y)
    (M : ℕ) (hM : 0<M) (hm : ∀ c : R,ChunkComparisons.multiplicity col c ≤ M) :
    (∑ j : Fin M, ((Fintype.card (ActiveV (S) m j.val):ℤ)-Fintype.card (A j.val)-
      if j.val=0 then Fintype.card {i : P // cyclic i=false} else 0)) ≤ 0 := by
  have hd : ∀ d,m d ≤ M := by
    intro d
    rw [multiplicity_at Γ mark h2 paths]
    exact hm _
  have h := ListStageExponents.exponent_nonpos (S) paths hp cyclic hc hclose M hM hd
  simpa only [ListStageExponents.mult,edges_card Γ mark h2 paths] using h

end TorsionFreeZeroDivisors.ChainActiveStages

namespace TorsionFreeZeroDivisors.SubdivisionRestriction
open scoped Classical
open ChainSubdivision
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
    (active : C → Prop) (incident : V → Prop)
    (hf : ∀ c,active c → incident (first c))
    (hl : ∀ c,active c → incident (last c))

abbrev length : {c // active c} → ℕ := fun c => len c.val

local notation "P" => graph len first last

def dart : Dart (length len active) → Dart len := fun d => (⟨d.1.1.val,d.1.2⟩,d.2)

lemma dart_injective : Function.Injective (dart len active) := by
  rintro ⟨⟨⟨c,hc⟩,i⟩,r⟩ ⟨⟨⟨d,hd⟩,k⟩,s⟩ h
  have hrs := congrArg Prod.snd h
  cases hrs
  have h' := congrArg Prod.fst h
  have hcd := congrArg Sigma.fst h'
  cases hcd
  have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
  cases hik
  rfl

end TorsionFreeZeroDivisors.SubdivisionRestriction

namespace TorsionFreeZeroDivisors.ChainStageEmbedding
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths
local notation "e" => ListStageExponents.edge paths
local notation "m" => StageSubgraphs.multiplicity (S) e
local notation "A" => ChainActiveStages.ActiveChain Γ mark h2 paths j
local notation "W" => ActiveV (S) m j

abbrev length : A → ℕ := fun c => repLength Γ mark h2 c.val
abbrev graph := ChainSubdivision.graph (length Γ mark h2 paths j)
  (ChainActiveStages.first Γ mark h2 paths j) (ChainActiveStages.last Γ mark h2 paths j)
local notation "Q" => graph Γ mark h2 paths j

abbrev active (c : R) : Prop := j<ChunkComparisons.multiplicity col c
def marked (v : W) : Mark mark := ⟨v.val,by
  rcases v.property with ⟨d,hd,_⟩
  rw [←hd]
  exact (turn_fixed_iff Γ.origin mark h2 d.val).mp d.property⟩

lemma marked_injective : Injective (marked Γ mark h2 paths j) := by
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : Mark mark => z.val) h

def vertexLift : ChainSubdivision.Vertex (length Γ mark h2 paths j) (V := W) →
    ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark)
  | .inl v => .inl (marked Γ mark h2 paths j v)
  | .inr ⟨c,i⟩ => .inr ⟨c.val,i⟩

lemma vertexLift_injective : Injective (vertexLift Γ mark h2 paths j) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => exact congrArg Sum.inl (marked_injective Γ mark h2 paths j (Sum.inl.inj h))
    | inr w => cases h
  | inr v =>
    cases w with
    | inl w => cases h
    | inr w =>
      rcases v with ⟨⟨c,hc⟩,i⟩
      rcases w with ⟨⟨d,hd⟩,k⟩
      have h' := Sum.inr.inj h
      have hcd := congrArg Sigma.fst h'
      cases hcd
      have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
      cases hik
      rfl

lemma point_lift (c : A) (k : Fin ((length Γ mark h2 paths j) c+1)) :
    vertexLift Γ mark h2 paths j
      (ChainSubdivision.point (length Γ mark h2 paths j)
        (ChainActiveStages.first Γ mark h2 paths j) (ChainActiveStages.last Γ mark h2 paths j) c k) =
      ChainSubdivision.point (repLength Γ mark h2) (ChainIsomorphism.first Γ mark h2)
        (ChainIsomorphism.last Γ mark h2) c.val k := by
  unfold ChainSubdivision.point
  split_ifs <;> rfl

def vertexMap : ChainSubdivision.Vertex (length Γ mark h2 paths j) (V := W) → V :=
  ChainIsomorphism.vertexMap Γ mark h2 ∘ vertexLift Γ mark h2 paths j

def dartMap : ChainSubdivision.Dart (length Γ mark h2 paths j) → D :=
  ChainIsomorphism.dartMap Γ mark h2 ∘ SubdivisionRestriction.dart (repLength Γ mark h2)
    (active Γ mark h2 paths j)

lemma vertexMap_injective : Injective (vertexMap Γ mark h2 paths j) :=
  (ChainIsomorphism.vertexMap_injective Γ mark h2).comp
    (vertexLift_injective Γ mark h2 paths j)

lemma dartMap_injective : Injective (dartMap Γ mark h2 paths j) :=
  (ChainIsomorphism.dartMap_injective Γ mark h2).comp
    (SubdivisionRestriction.dart_injective _ _)

lemma origin_map (d : ChainSubdivision.Dart (length Γ mark h2 paths j)) :
    vertexMap Γ mark h2 paths j ((Q).origin d)=Γ.origin (dartMap Γ mark h2 paths j d) := by
  unfold vertexMap dartMap
  dsimp only [Function.comp_apply]
  have h : vertexLift Γ mark h2 paths j ((Q).origin d) =
      (ChainSubdivision.graph (repLength Γ mark h2) (ChainIsomorphism.first Γ mark h2)
        (ChainIsomorphism.last Γ mark h2)).origin
        (SubdivisionRestriction.dart (repLength Γ mark h2) (active Γ mark h2 paths j) d) := by
    rcases d with ⟨⟨c,i⟩,r⟩
    cases r
    · simpa only [SubdivisionRestriction.dart,ChainSubdivision.origin_forward] using
        point_lift Γ mark h2 paths j c ⟨i.val,by have h:=i.isLt; omega⟩
    · simpa only [SubdivisionRestriction.dart,ChainSubdivision.origin_backward] using
        point_lift Γ mark h2 paths j c ⟨i.val+1,by have h:=i.isLt; omega⟩
  rw [h]
  exact ChainIsomorphism.origin_map Γ mark h2 _

lemma reverse_map (d : ChainSubdivision.Dart (length Γ mark h2 paths j)) :
    dartMap Γ mark h2 paths j ((Q).reverse d)=Γ.reverse (dartMap Γ mark h2 paths j d) := by
  unfold dartMap
  dsimp only [Function.comp_apply]
  rw [show SubdivisionRestriction.dart (repLength Γ mark h2) (active Γ mark h2 paths j) ((Q).reverse d)=
      (ChainSubdivision.graph (repLength Γ mark h2) (ChainIsomorphism.first Γ mark h2)
        (ChainIsomorphism.last Γ mark h2)).reverse
        (SubdivisionRestriction.dart (repLength Γ mark h2) (active Γ mark h2 paths j) d) from rfl]
  exact ChainIsomorphism.dartMap_reverse Γ mark h2 _

end TorsionFreeZeroDivisors.ChainStageEmbedding

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical BigOperators
variable {V T : Type*} [Fintype V]

def free (root : Option V) (target : T) : ℕ :=
  (Finset.univ.filter fun v => pin root target v=none).card

lemma free_none (target : T) : free (V:=V) none target=Fintype.card V := by
  simp [free,pin]

lemma free_some (root : V) (target : T) : free (some root) target+1=Fintype.card V := by
  have h : (Finset.univ.filter fun v => pin (some root) target v=none) = Finset.univ.erase root := by
    ext v
    simp [pin,eq_comm]
  unfold free
  rw [h,Finset.card_erase_add_one (Finset.mem_univ root),Finset.card_univ]

lemma free_cast (root : Option V) (target : T) :
    (free root target : ℤ)=(Fintype.card V:ℤ)-(if root.isSome then 1 else 0) := by
  cases root with
  | none => simp only [free_none,Option.isSome_none,Bool.false_eq_true,ite_false,sub_zero]
  | some v =>
    have h := free_some v target
    simp only [Option.isSome_some,ite_true]
    omega

end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.ActiveRoot
open scoped Classical
open PortSubdivision StageSubgraphs
variable {V D P : Type*} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (paths : P → List D) (hp : ∀ p,paths p≠[])

omit [Fintype D] in
lemma occurrence_positive (p : P) (i : Fin (paths p).length) :
    0<ListStageExponents.mult Γ paths ((paths p).get i) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨p,i,false⟩,rfl⟩⟩

/-- The actual initial vertex belongs to the first active stage. -/
def vertex (p : P) : ActiveV Γ (ListStageExponents.mult Γ paths) 0 :=
  let i : Fin (paths p).length := ⟨0,List.length_pos_iff.mpr (hp p)⟩
  ⟨Γ.origin ((paths p).get i),(paths p).get i,rfl,occurrence_positive Γ paths p i⟩

omit [Fintype D] in
@[simp] lemma vertex_val (p : P) :
    (vertex Γ paths hp p).val=Γ.origin ((paths p).head (hp p)) := by
  simp [vertex,List.head_eq_getElem]

end TorsionFreeZeroDivisors.ActiveRoot

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.LinkComponents
open scoped Classical BigOperators
open EntropyStages
variable {I : Type*} [Fintype I] (m : I → ℕ)
abbrev Occurrence := (i : I) × Fin (m i)
variable (P : Pairing (Occurrence m))

def graph : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ o : Occurrence m, o.1 = i ∧ (P.partner o).1 = j
  symm := ⟨by
    rintro i j ⟨hne,o,hi,hj⟩
    exact ⟨hne.symm,P.partner o,hj,by rw [P.involutive]; exact hi⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

abbrev Component := (graph m P).ConnectedComponent

def HasSelf (c : Component m P) : Prop :=
  ∃ o : Occurrence m, (graph m P).connectedComponentMk o.1 = c ∧
    P.partner o ≠ o ∧ (P.partner o).1 = o.1

omit [Fintype I] in
/-- Matched block occurrences always stay in their link component. -/
theorem partner_component (o : Occurrence m) :
    (graph m P).connectedComponentMk (P.partner o).1 = (graph m P).connectedComponentMk o.1 := by
  by_cases he : (P.partner o).1 = o.1
  · rw [he]
  · apply SimpleGraph.ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    exact ⟨he,P.partner o,rfl,by rw [P.involutive]⟩

abbrev ComponentOccurrence (c : Component m P) :=
  {o : Occurrence m // (graph m P).connectedComponentMk o.1 = c}

def restrict (c : Component m P) : Pairing (ComponentOccurrence m P c) where
  partner o := ⟨P.partner o.val,(partner_component m P o.val).trans o.property⟩
  involutive o := Subtype.ext (P.involutive o.val)

def unmatched (c : Component m P) : ℕ := Fintype.card (restrict m P c).Unmatched

/-- Counting actual occurrences, including repeats, gives the sum of block
multiplicities in the component. -/
theorem card_occurrences (c : Component m P) :
    Fintype.card (ComponentOccurrence m P c) = ∑ i : c, m i.val := by
  let e : ComponentOccurrence m P c ≃ (i : c) × Fin (m i.val) :=
    { toFun := fun o => ⟨⟨o.val.1,o.property⟩,o.val.2⟩
      invFun := fun o => ⟨⟨o.1.val,o.2⟩,o.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem card_block_occurrences (c : Component m P) (i : c) :
    Fintype.card {o : ComponentOccurrence m P c // o.val.1 = i.val} = m i.val := by
  let e : {o : ComponentOccurrence m P c // o.val.1 = i.val} ≃ Fin (m i.val) :=
    { toFun := fun o => ⟨o.val.val.2.val,by simpa only [o.property] using o.val.val.2.isLt⟩
      invFun := fun k => ⟨⟨⟨i.val,k⟩,i.property⟩,rfl⟩
      left_inv := by
        intro ⟨⟨⟨j,k⟩,hj⟩,hi⟩
        dsimp at hi
        subst j
        rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- Literal link balance in a component without a self-link. -/
theorem balance (c : Component m P) (hn : ¬HasSelf m P c) (i : c) :
    2*m i.val ≤ (∑ j : c, m j.val) + unmatched m P c := by
  have hc : ∀ o : ComponentOccurrence m P c,
      (restrict m P c).partner o ≠ o →
        ((restrict m P c).partner o).val.1 ≠ o.val.1 := by
    intro o hne he
    apply hn
    exact ⟨o.val,o.property,fun ho => hne (Subtype.ext ho),he⟩
  have hh := (restrict m P c).color_balance (fun o => o.val.1) i.val hc
  rw [card_block_occurrences m P c i,card_occurrences m P c] at hh
  exact hh

/-- The maximum multiplicity is present exactly in the active components. -/
def maximum (c : Component m P) : ℕ :=
  (Finset.univ.image (fun i : c => m i.val)).max'
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨m i.val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)

theorem le_maximum (c : Component m P) (i : c) : m i.val ≤ maximum m P c :=
  by
    unfold maximum
    exact Finset.le_max' (Finset.univ.image (fun j : c => m j.val)) (m i.val) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem maximum_mem (c : Component m P) : ∃ i : c, m i.val = maximum m P c := by
  have hh := Finset.max'_mem (Finset.univ.image (fun i : c => m i.val))
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨m i.val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  rcases Finset.mem_image.mp hh with ⟨i,_,hi⟩
  exact ⟨i,hi⟩

theorem maximum_balance (c : Component m P) (hn : ¬HasSelf m P c) :
    2*maximum m P c ≤ (∑ j : c, m j.val) + unmatched m P c := by
  obtain ⟨i,hi⟩ := maximum_mem m P c
  rw [← hi]
  exact balance m P c hn i

theorem active_iff (c : Component m P) (j : ℕ) :
    (∃ i : c, j < m i.val) ↔ j < maximum m P c := by
  constructor
  · rintro ⟨i,hi⟩
    exact hi.trans_le (le_maximum m P c i)
  · intro hj
    obtain ⟨i,hi⟩ := maximum_mem m P c
    exact ⟨i,hi ▸ hj⟩

/-- Components partition the underlying blocks, including the isolated ones. -/
theorem sum_components {R : Type*} [AddCommMonoid R] (a : I → R) :
    (∑ c : Component m P, ∑ i : c, a i.val) = ∑ i, a i := by
  let e := Equiv.sigmaFiberEquiv (graph m P).connectedComponentMk
  calc
    _ = ∑ x : (c : Component m P) × c, a x.2.val :=
      (Fintype.sum_sigma (fun x : (c : Component m P) × c => a x.2.val)).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Fixed occurrences are partitioned by precisely the same components. -/
theorem sum_unmatched :
    (∑ c : Component m P, unmatched m P c) = Fintype.card P.Unmatched := by
  let f : P.Unmatched → Component m P := fun o => (graph m P).connectedComponentMk o.val.1
  have hc (c : Component m P) :
      unmatched m P c = Fintype.card {o : P.Unmatched // f o = c} := by
    let e : (restrict m P c).Unmatched ≃ {o : P.Unmatched // f o = c} :=
      { toFun := fun o => ⟨⟨o.val.val, congrArg Subtype.val o.property⟩, o.val.property⟩
        invFun := fun o => ⟨⟨o.val.val, o.property⟩, Subtype.ext o.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  simp_rw [hc]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- The bin-minimizing root need not be present at a given stage. -/
def minimumRoot (d : I → ℝ) (c : Component m P) : c :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun i : c => d i.val)
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨i, Finset.mem_univ _⟩))

theorem minimumRoot_le (d : I → ℝ) (c : Component m P) (i : c) :
    d (minimumRoot m P d c).val ≤ d i.val :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ (fun i : c => d i.val)
    (by obtain ⟨i⟩ := c.connected_toSimpleGraph.nonempty; exact ⟨i, Finset.mem_univ _⟩))).2 i (Finset.mem_univ _)

def componentLabelCost (d : I → ℝ) (δ s : ℝ) (c : Component m P) : ℝ :=
  if HasSelf m P c then 0 else 2*d (minimumRoot m P d c).val-δ*s

/-- The actual label/block part of the stage exponent, before embedding and
uniform error terms are added. Stages are indexed from zero. -/
def stageCost (M : ℕ) (d : I → ℝ) (δ s : ℝ) (j : Fin M) : ℝ :=
  -(∑ i, if j.val < m i then d i else 0) +
    ∑ c : Component m P, if j.val < maximum m P c then componentLabelCost m P d δ s c else 0

/-- Summing the actual link-component exponents gives decay and
only the globally counted unmatched correction. No coverage identity is assumed. -/
theorem sum_stageCost (M : ℕ) (hm : ∀ i, m i ≤ M) (d : I → ℝ) (δ s a : ℝ)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hlow : ∀ i, δ*s/2 ≤ d i) (hhigh : ∀ i, d i ≤ a*s) :
    (∑ j : Fin M, stageCost m P M d δ s j) ≤
      a*s*(Fintype.card P.Unmatched : ℝ) - δ/2*s*(∑ i, (m i : ℝ)) := by
  have hz : ∀ c : Component m P, maximum m P c ≤ M := by
    intro c
    obtain ⟨i,hi⟩ := maximum_mem m P c
    rw [← hi]
    exact hm i.val
  have hi : (∑ j : Fin M, ∑ i, if j.val < m i then d i else 0) =
      ∑ i, (m i : ℝ)*d i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => StageFusion.layers M (m i) (hm i) (d i))
  have hc : (∑ j : Fin M, ∑ c : Component m P,
      if j.val < maximum m P c then componentLabelCost m P d δ s c else 0) =
      ∑ c : Component m P, (maximum m P c : ℝ)*componentLabelCost m P d δ s c := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => StageFusion.layers M (maximum m P c) (hz c) _)
  have hid : (∑ j : Fin M, stageCost m P M d δ s j) =
      ∑ c : Component m P, StageFusion.componentCost (HasSelf m P)
        (fun (c : Component m P) (i : c) => m i.val) (fun (c : Component m P) (i : c) => d i.val) (maximum m P)
        (fun c => d (minimumRoot m P d c).val) δ s c := by
    simp only [stageCost,Finset.sum_add_distrib,Finset.sum_neg_distrib]
    rw [hi,hc,← sum_components m P (fun i => (m i : ℝ)*d i)]
    simp only [StageFusion.componentCost,Finset.sum_add_distrib,Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    unfold componentLabelCost
    split_ifs <;> ring
  rw [hid]
  have htotal := StageFusion.total_component_cost (HasSelf m P)
    (fun (c : Component m P) (i : c) => m i.val) (fun (c : Component m P) (i : c) => d i.val) (maximum m P)
    (fun c => d (minimumRoot m P d c).val) (fun c => (unmatched m P c : ℝ)) δ s a
    hδ hs ha (fun _ => Nat.cast_nonneg _)
    (fun _ i => hlow i.val) (fun c _ i => minimumRoot_le m P d c i)
    (fun c _ => hlow (minimumRoot m P d c).val)
    (fun c _ => hhigh (minimumRoot m P d c).val)
    (fun c hc => by exact_mod_cast maximum_balance m P c hc)
  have hu : (∑ c : Component m P, (unmatched m P c : ℝ)) = Fintype.card P.Unmatched := by
    exact_mod_cast sum_unmatched m P
  rw [hu,sum_components m P (fun i => (m i : ℝ))] at htotal
  exact htotal

/-- A numerical bound for actual stages: the Euler terms need only have
nonpositive total, exactly as supplied by the immersed traversal argument. -/
theorem sum_stageBound (M : ℕ) (hm : ∀ i, m i ≤ M) (d : I → ℝ) (δ s a logn : ℝ)
    (power err : Fin M → ℝ)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hn : 0 ≤ logn)
    (hlow : ∀ i, δ*s/2 ≤ d i) (hhigh : ∀ i, d i ≤ a*s)
    (hpower : (∑ j : Fin M, power j) ≤ 0) :
    (Finset.univ.sum (fun j : Fin M => power j*logn + stageCost m P M d δ s j + err j)) ≤
      a*s*(Fintype.card P.Unmatched : ℝ) - δ/2*s*(∑ i, (m i : ℝ)) + (∑ j : Fin M, err j) := by
  have hc := sum_stageCost m P M hm d δ s a hδ hs ha hlow hhigh
  have hp := mul_nonpos_of_nonpos_of_nonneg hpower hn
  simp only [Finset.sum_add_distrib,← Finset.sum_mul]
  linarith

end TorsionFreeZeroDivisors.LinkComponents

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*} (D : OccurrenceMatching.Data (Ω := Ω) (B := B) (E := E))

def transport (r : B' ≃ B) : OccurrenceMatching.Data (Ω := Ω) (B := B') (E := E) where
  error := D.error
  positions b := D.positions (r b)
  disjoint h := D.disjoint (r.injective.ne h)
  pairing := D.pairing
  side := D.side
  flip := D.flip
  flip_inv := D.flip_inv
  flip_ne := D.flip_ne
  side_partner := D.side_partner

theorem transport_joined (r : B' ≃ B) (o p : B') :
    (D.transport r).Joined o p ↔ D.Joined (r o) (r p) := Iff.rfl

theorem transport_partner (r : B' ≃ B) (o : B') :
    r ((D.transport r).matching.partner o) = D.matching.partner (r o) := by
  by_cases h : D.matching.partner (r o) = r o
  · have hh : (D.transport r).matching.partner o = o := by
      apply ((D.transport r).unmatched_iff o).mpr
      intro p hp
      exact (D.unmatched_iff (r o)).mp h (r p) hp
    rw [hh,h]
  · obtain ⟨p,hp⟩ := (D.matched_iff (r o)).mp h
    have hp' : (D.transport r).Joined o (r.symm p) := by
      rw [transport_joined,r.apply_symm_apply]
      exact hp
    have he := (D.transport r).partner_spec hp'
    have he' := D.partner_spec hp
    change (D.transport r).matching.partner o = r.symm p at he
    change D.matching.partner (r o) = p at he'
    rw [he,he',r.apply_symm_apply]

end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.RepeatedBlocks
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {C E : Type*} (s : ℝ) (hs : 0 < s) (len m : C → ℕ)

abbrev traversalLength : Traversal m → ℕ := fun t => len t.1
abbrev Underlying := ComparedBlocks.Block s len
abbrev Occurrence := ComparedBlocks.Block s (traversalLength len m)
abbrev multiplicity (i : Underlying s len) : ℕ := m i.1

/-- The occurrence index is retained separately from the common chain grid. -/
def occurrenceEquiv : Occurrence s len m ≃ LinkComponents.Occurrence (multiplicity s len m) where
  toFun b := ⟨⟨b.1.1,b.2⟩,b.1.2⟩
  invFun b := ⟨⟨b.1.1,b.2⟩,b.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def color (b : Occurrence s len m) : Underlying s len := (occurrenceEquiv s len m b).1

def height (i : Underlying s len) : ℕ := (block s i.2.val).card

def lower (i : Underlying s len) : ℤ := ⌈(i.2.val : ℝ)*s-1/2⌉
def upper (i : Underlying s len) : ℤ := ⌈((i.2.val : ℝ)+1)*s-1/2⌉

theorem block_interval (i : Underlying s len) : block s i.2.val = Finset.Ico (lower s len i) (upper s len i) := by
  simp only [block,positions,lower,upper,Int.cast_natCast]

/-- Literal increasing edge coordinates shared by every repetition. -/
def wordCoordinate (i : Underlying s len) : block s i.2.val ≃ Fin (height s len i) :=
  (Equiv.setCongr (congrArg (fun positions : Finset ℤ => (positions : Set ℤ)) (block_interval s len i))).trans
    ((IntervalSelfLinks.coordinate (lower s len i) (upper s len i)).trans
      (finCongr (by rw [height,block_interval,Int.card_Ico])))

theorem wordCoordinate_val (i : Underlying s len) (q : block s i.2.val) :
    ((wordCoordinate s len i q).val : ℤ) = q.val-lower s len i := by
  exact IntervalSelfLinks.coordinate_val ⟨q.val,by rw [← block_interval]; exact q.property⟩

def blockPositionEquiv (b : Occurrence s len m) :
    blockPositions s hs (traversalLength len m) b ≃ block s b.2.val where
  toFun x := ⟨x.val.2.val,((mem_blockPositions s hs (traversalLength len m)).mp x.property).2⟩
  invFun q := ⟨includeBlock s hs (traversalLength len m) b q,
    Finset.mem_map.mpr ⟨q,Finset.mem_attach _ _,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hh := ((mem_blockPositions s hs (traversalLength len m)).mp x.property).1
    cases b with
    | mk t k =>
      rcases x with ⟨⟨u,q⟩,hx⟩
      dsimp at hh
      subst u
      rfl
  right_inv _ := rfl

def coordinate (b : Occurrence s len m) :
    blockPositions s hs (traversalLength len m) b ≃ Fin (height s len (color s len m b)) :=
  (blockPositionEquiv s hs len m b).trans (wordCoordinate s len (color s len m b))

theorem coordinate_val (b : Occurrence s len m)
    (x : blockPositions s hs (traversalLength len m) b) :
    ((coordinate s hs len m b x).val : ℤ) = x.val.2.val-lower s len (color s len m b) :=
  wordCoordinate_val s len (color s len m b) (blockPositionEquiv s hs len m b x)

variable (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def data : OccurrenceMatching.Data (Ω := Position (traversalLength len m))
    (B := LinkComponents.Occurrence (multiplicity s len m)) (E := E) :=
  (cmp.matchingData s hs (traversalLength len m) err).transport (occurrenceEquiv s len m).symm

def repeatedCoordinate (b : LinkComponents.Occurrence (multiplicity s len m)) :
    (data s hs len m cmp err).positions b ≃ Fin (height s len b.1) :=
  coordinate s hs len m ((occurrenceEquiv s len m).symm b)

variable {A : Type*} (symbol : E → (A ≃ A))

def links : StageLabels.Links (T := A) (height s len) :=
  MatchedLabels.links (data s hs len m cmp err) Sigma.fst (height s len)
    (repeatedCoordinate s hs len m cmp err) symbol

theorem links_deficit (i j : Underlying s len)
    (hadj : (links s hs len m cmp err symbol).graph.Adj i j) :
    height s len i - ((links s hs len m cmp err symbol).known i j).card ≤ err :=
  MatchedLabels.links_deficit _ _ _ _ _ hadj

theorem links_consistent (letters : Position (traversalLength len m) → A)
    (words : (i : Underlying s len) → Fin (height s len i) → A)
    (hcompare : ∀ x e, cmp.side x = some e →
      letters x = symbol e (letters (cmp.pairing.partner x)))
    (hwords : ∀ b (x : blockPositions s hs (traversalLength len m) b),
      words (color s len m b) (coordinate s hs len m b x) = letters x.val) :
    (links s hs len m cmp err symbol).Consistent words := by
  apply MatchedLabels.links_consistent _ _ _ _ _ letters words hcompare
  intro b x
  exact hwords ((occurrenceEquiv s len m).symm b) x

theorem integerSlice_self (i : Underlying s len) (k t : Fin (m i.1)) (e : E) :
    cmp.integerSlice s (traversalLength len m) e
      ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩) =
    IntervalSelfLinks.selfSlice (lower s len i) (upper s len i)
      ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.reverse e) (cmp.offset e) := by
  unfold Comparisons.integerSlice
  change (block s i.2.val ∩ positions (cmp.lo e) (cmp.hi e)).filter
    (fun q => affine (cmp.reverse e) (cmp.offset e) q ∈ block s i.2.val) = _
  rw [block_interval s len i]
  rfl

 theorem self_slice_card (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hsource : (⟨i.1,k⟩ : Traversal m) = cmp.source e)
    (htarget : (⟨i.1,t⟩ : Traversal m) = cmp.source (cmp.flip e)) :
    ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card =
      (IntervalSelfLinks.selfSlice (lower s len i) (upper s len i)
        ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.reverse e) (cmp.offset e)).card := by
  change ((cmp.matchingData s hs (traversalLength len m) err).slice e
    ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩)).card = _
  rw [cmp.slice_integer_card s hs (traversalLength len m) err hsource htarget,
    integerSlice_self]

include hs in
/-- The original letter comparison restricts to precisely this integer slice. -/
theorem self_comparison {A : Type*} (bar : A → A) (w : C → ℤ → A)
    (hcompare : ∀ x e, cmp.side x = some e →
      w x.1.1 x.2.val = if cmp.reverse e then
        bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
      else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hsource : (⟨i.1,k⟩ : Traversal m) = cmp.source e)
    (htarget : (⟨i.1,t⟩ : Traversal m) = cmp.source (cmp.flip e))
    (q : ℤ) (hq : q ∈ IntervalSelfLinks.selfSlice (lower s len i) (upper s len i)
      ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.reverse e) (cmp.offset e)) :
    w i.1 q = if cmp.reverse e then bar (w i.1 (affine (cmp.reverse e) (cmp.offset e) q))
      else w i.1 (affine (cmp.reverse e) (cmp.offset e) q) := by
  have hh := (Finset.mem_inter.mp (Finset.mem_filter.mp hq).1)
  have hb : q ∈ block s i.2.val := by rw [block_interval]; exact hh.1
  let x : Position (traversalLength len m) :=
    ⟨⟨i.1,k⟩,⟨q,full_subset s hs (len i.1) i.2 hb⟩⟩
  have hx : cmp.side x = some e := (cmp.side_iff x e).mpr ⟨hsource,hh.2⟩
  have hy : (cmp.pairing.partner x).1.1 = i.1 :=
    congrArg Sigma.fst ((cmp.partner_source x e hx).trans htarget.symm)
  have hc := hcompare x e hx
  rw [hy,cmp.partner_coordinate x e hx] at hc
  exact hc

/-- Literal edge reduction rules out zero shift, rather than assuming that
self-links are nontrivial translations. -/
theorem self_shift_ne_zero
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hne : ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).Nonempty)
    (hrev : cmp.reverse e = false) : cmp.offset e ≠ 0 := by
  intro hz
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hb,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
  have hb' := ((mem_blockPositions s hs (traversalLength len m)).mp hb).1
  have hp' := ((mem_blockPositions s hs (traversalLength len m)).mp hp).1
  apply hreduced x e he
  apply Prod.ext
  · exact (congrArg Sigma.fst hb').trans (congrArg Sigma.fst hp').symm
  · rw [cmp.partner_coordinate x e he]
    simp [affine,hrev,hz]

/-- A near-full actual self-link is a nonzero translation. Reversed self-links
are infeasible for an immersed block, by the midpoint obstruction. -/
theorem self_link_translation {A : Type*} (bar : A → A)
    (hbar : Function.Involutive bar) (hfree : ∀ a, bar a ≠ a)
    (w : C → ℤ → A)
    (hcompare : ∀ x e, cmp.side x = some e →
      w x.1.1 x.2.val = if cmp.reverse e then
        bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
      else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    (hwordred : ∀ (i : Underlying s len) q,
      lower s len i ≤ q → q+1 < upper s len i → w i.1 (q+1) ≠ bar (w i.1 q))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hmass : height s len i < 2*((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card) :
    cmp.reverse e = false ∧ cmp.offset e ≠ 0 := by
  have hne : ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hne' : ((cmp.matchingData s hs (traversalLength len m) err).slice e
    ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩)).Nonempty := hne
  obtain ⟨hsrc,htgt⟩ := cmp.slice_sources s hs (traversalLength len m) err hne'
  have hrev : cmp.reverse e = false := by
    cases hr : cmp.reverse e with
    | false => rfl
    | true =>
      have hh := IntervalSelfLinks.reflection_not_large bar hbar hfree (w i.1)
        (lower s len i) (upper s len i) ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.offset e)
        (hwordred i) (by
          intro q hq
          have hc := self_comparison s hs len m cmp bar w hcompare i k t e hsrc htgt q (by rwa [hr])
          simpa [hr,affine] using hc)
      rw [self_slice_card s hs len m cmp err i k t e hsrc htgt,hr] at hmass
      change (block s i.2.val).card < _ at hmass
      rw [block_interval] at hmass
      omega
  exact ⟨hrev,self_shift_ne_zero s hs len m cmp err hreduced i k t e hne hrev⟩

theorem height_eq (i : Underlying s len) :
    height s len i = (upper s len i-lower s len i).toNat := by
  rw [height,block_interval,Int.card_Ico]

/-- The actual word on an underlying block, in its chain orientation. -/
def word (w : C → ℤ → A) (i : Underlying s len) (k : Fin (height s len i)) : A :=
  w i.1 ((k.val : ℤ)+lower s len i)

theorem word_at_coordinateN (w : C → ℤ → A) (i : Underlying s len)
    (q : Finset.Ico (lower s len i) (upper s len i)) :
    word s len w i (IntervalSelfLinks.coordinateN (lower s len i) (upper s len i)
      (height s len i) (height_eq s len i) q) = w i.1 q.val := by
  unfold word
  rw [IntervalSelfLinks.coordinateN_val,sub_add_cancel]

/-- A chosen literal self-comparison yields a fixed translation forest that
works for all compatible words. Its cardinality is the original slice's, not
an unrelated proxy for the number of constraints. -/
theorem self_translation_constraints
    (i : Underlying s len) (k t : Fin (m i.1)) (e : E)
    (hsource : (⟨i.1,k⟩ : Traversal m) = cmp.source e)
    (htarget : (⟨i.1,t⟩ : Traversal m) = cmp.source (cmp.flip e))
    (hrev : cmp.reverse e = false) (hz : cmp.offset e ≠ 0) :
    ∃ tr : BlockConstraints.Translation (height s len i),
      tr.domain.card = ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card ∧
      ∀ (A : Type*) (bar : A → A) (w : C → ℤ → A),
        (∀ x e, cmp.side x = some e →
          w x.1.1 x.2.val = if cmp.reverse e then
            bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
          else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val) →
        ∀ q : tr.domain, word s len w i (tr.target q) = word s len w i q.val := by
  obtain ⟨tr,hcard,htr⟩ := IntervalSelfLinks.translation_from_slice_at
    (lower s len i) (upper s len i) ⌈cmp.lo e-1/2⌉ ⌈cmp.hi e-1/2⌉ (cmp.offset e) hz
    (height s len i) (height_eq s len i)
  refine ⟨tr,?_,?_⟩
  · rw [hcard,self_slice_card s hs len m cmp err i k t e hsource htarget,hrev]
  · intro A bar w hcompare
    apply htr A (word s len w i)
    intro q hq
    rw [word_at_coordinateN,word_at_coordinateN]
    have hc := self_comparison s hs len m cmp bar w hcompare i k t e hsource htarget q (by rwa [hrev])
    simpa [hrev,affine] using hc.symm

theorem positions_height (o : LinkComponents.Occurrence (multiplicity s len m)) :
    ((data s hs len m cmp err).positions o).card = height s len o.1 := by
  have hh := Fintype.card_congr (repeatedCoordinate s hs len m cmp err o)
  simpa only [Fintype.card_coe,Fintype.card_fin] using hh

/-- Every literal self-linked component has a root and a translation forest
of the prescribed deficit. A single feasible immersed labeling rules out the
reflection case; the resulting forest then constrains every feasible labeling. -/
theorem self_component_translation [Fintype C]
    {A : Type*} (bar : A → A) (hbar : Function.Involutive bar) (hfree : ∀ a, bar a ≠ a)
    (w₀ : C → ℤ → A)
    (hcompare₀ : ∀ x e, cmp.side x = some e →
      w₀ x.1.1 x.2.val = if cmp.reverse e then
        bar (w₀ (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
      else w₀ (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    (hwordred : ∀ (i : Underlying s len) q,
      lower s len i ≤ q → q+1 < upper s len i → w₀ i.1 (q+1) ≠ bar (w₀ i.1 q))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (c : LinkComponents.Component (multiplicity s len m) (data s hs len m cmp err).matching)
    (hc : LinkComponents.HasSelf (multiplicity s len m) (data s hs len m cmp err).matching c) :
    ∃ (i : c) (tr : BlockConstraints.Translation (height s len i.val)),
      height s len i.val-tr.domain.card ≤ err ∧
      ∀ (A : Type*) (bar : A → A) (w : C → ℤ → A),
        (∀ x e, cmp.side x = some e →
          w x.1.1 x.2.val = if cmp.reverse e then
            bar (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
          else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val) →
        ∀ q : tr.domain, word s len w i.val (tr.target q) = word s len w i.val q.val := by
  obtain ⟨o,ho,hmatched,hself⟩ := hc
  obtain ⟨p,hjoin⟩ := ((data s hs len m cmp err).matched_iff o).mp hmatched
  have hp := (data s hs len m cmp err).partner_spec hjoin
  change (data s hs len m cmp err).partner o = p at hp
  change ((data s hs len m cmp err).partner o).1 = o.1 at hself
  rw [hp] at hself
  rcases o with ⟨i,k⟩
  rcases p with ⟨j,t⟩
  dsimp at hself
  subst j
  obtain ⟨e,hmass,_,hdef,_⟩ := hjoin
  rw [positions_height] at hmass hdef
  obtain ⟨hr,hz⟩ := self_link_translation s hs len m cmp err bar hbar hfree w₀
    hcompare₀ hwordred hreduced i k t e hmass
  have hne : ((cmp.matchingData s hs (traversalLength len m) err).slice e
    ((occurrenceEquiv s len m).symm ⟨i,k⟩) ((occurrenceEquiv s len m).symm ⟨i,t⟩)).Nonempty :=
    Finset.card_pos.mp (by change 0 < ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card; omega)
  obtain ⟨hsrc,htgt⟩ := cmp.slice_sources s hs (traversalLength len m) err hne
  obtain ⟨tr,hcard,htr⟩ := self_translation_constraints s hs len m cmp err i k t e hsrc htgt hr hz
  refine ⟨⟨i,ho⟩,tr,?_,htr⟩
  rw [hcard]
  change height s len i ≤ ((data s hs len m cmp err).slice e ⟨i,k⟩ ⟨i,t⟩).card+err at hdef
  exact Nat.sub_le_iff_le_add.mpr (by simpa only [Nat.add_comm] using hdef)

end TorsionFreeZeroDivisors.RepeatedBlocks

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageBlocks
open scoped BigOperators Classical
open StageLabels WordEstimate
variable {I : Type*} [Fintype I] {h : I → ℕ}
variable (L : Links (T := Letter) h)

def translationWords {n : ℕ} (D : BlockConstraints.Translation n) : Finset (Fin n → Letter) :=
  Finset.univ.filter (fun W => ∀ i : D.domain, W (D.target i) = W i.val)

theorem translation_card {n : ℕ} (D : BlockConstraints.Translation n) :
    (translationWords D).card ≤ (Fintype.card Letter)^(n-D.domain.card) := by
  have he : {W : Fin n → Letter // W ∈ translationWords D} ≃
      {W : Fin n → Letter // ∀ i : D.domain, W (D.target i) = W i.val} :=
    Equiv.subtypeEquivRight (fun W => by simp [translationWords])
  have hh := D.word_count (T := Letter)
  rw [← Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_coe] at hh
  exact hh

variable (d : I → ℤ)

end TorsionFreeZeroDivisors.StageBlocks

namespace TorsionFreeZeroDivisors.ActualStageLabels

open scoped Classical BigOperators
section
/-- An infeasible complete word has no active projection. -/
theorem projection_empty {I T : Type*} [Fintype I] [Fintype T]
    (h : I → ℕ) (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop)
    (hn : ¬∃ W, P W) : StageLabels.stageWords h A P = ∅ := by
  unfold StageLabels.stageWords
  have he : Finset.univ.filter P = ∅ := by
    exact Finset.filter_eq_empty_iff.mpr (fun W _ hW => hn ⟨W,hW⟩)
  rw [he,Finset.image_empty]

/-- Uniform root errors and propagation errors together cost at most twice
one missing substring per underlying block. -/
theorem projection_bound {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]
    {h : I → ℕ} (L : StageLabels.Links (T := T) h) (A : Finset I)
    (r : (c : L.graph.ConnectedComponent) → c)
    (R : (c : L.graph.ConnectedComponent) → Finset (Fin (h (r c).val) → T))
    (P : ((i : I) → Fin (h i) → T) → Prop)
    (hP : ∀ w, P w → L.Consistent w)
    (hroot : ∀ w, P w → ∀ c, w (r c).val ∈ R c)
    (e : ℕ) (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e)
    (cost : L.graph.ConnectedComponent → ℝ)
    (hcost : ∀ c, ((R c).card : ℝ) ≤ Real.exp (cost c+(e : ℝ)*Real.log (Fintype.card T))) :
    ((StageLabels.stageWords h A P).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents L.graph.connectedComponentMk A, cost c.val) +
        2*(e : ℝ)*Fintype.card I*Real.log (Fintype.card T)) := by
  have hh := L.stage_exp A r R P hP hroot e he
    (fun c => cost c+(e : ℝ)*Real.log (Fintype.card T)) hcost
  apply hh.trans
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcomp : Fintype.card (StageLabels.activeComponents L.graph.connectedComponentMk A) ≤ Fintype.card I := by
    rw [Fintype.card_coe]
    exact (Finset.card_image_le).trans (Finset.card_le_univ _)
  have hall : (Fintype.card (StageLabels.activeComponents L.graph.connectedComponentMk A) : ℝ) ≤ Fintype.card I :=
    by exact_mod_cast hcomp
  have ha : 0 ≤ Real.log (Fintype.card T) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := T))
  have hel := mul_le_mul_of_nonneg_right hall (mul_nonneg (Nat.cast_nonneg e : (0:ℝ) ≤ e) ha)
  nlinarith
end
open scoped Classical BigOperators
open ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ)
variable (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def symbol (e : E) : Letter ≃ Letter :=
  if cmp.reverse e then ⟨inverse,inverse,inverse_inverse,inverse_inverse⟩ else Equiv.refl _

abbrev L := links s hs len m cmp err (symbol len m cmp)
abbrev P := (data s hs len m cmp err).matching
abbrev Component := LinkComponents.Component (multiplicity s len m) (P s hs len m cmp err)

def Comparing (w : C → ℤ → Letter) : Prop :=
  ∀ x e, cmp.side x = some e →
    w x.1.1 x.2.val = if cmp.reverse e then
      inverse (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val

def Immersed (w : C → ℤ → Letter) : Prop :=
  ∀ (i : Underlying s len) q,
    lower s len i ≤ q → q+1 < upper s len i → w i.1 (q+1) ≠ inverse (w i.1 q)

variable (d : Underlying s len → ℤ)

def Feasible (W : (i : Underlying s len) → Fin (height s len i) → Letter) : Prop :=
  (∀ i, W i ∈ binWords (height s len i) (d i)) ∧
    ∃ w : C → ℤ → Letter, Comparing len m cmp w ∧ Immersed s len w ∧ W = word s len w

omit [Fintype C] in
theorem feasible_consistent {W : (i : Underlying s len) → Fin (height s len i) → Letter}
    (hW : Feasible s len m cmp d W) : (L s hs len m cmp err).Consistent W := by
  obtain ⟨_,w,hw,_,rfl⟩ := hW
  apply links_consistent s hs len m cmp err (symbol len m cmp) (fun x => w x.1.1 x.2.val)
  · intro x e he
    have hh := hw x e he
    unfold symbol
    split_ifs with h
    · simpa [h] using hh
    · simpa [h] using hh
  · intro b x
    unfold word
    rw [coordinate_val,sub_add_cancel]
    have ht := ((mem_blockPositions s hs (traversalLength len m)).mp x.property).1
    exact congrArg (fun t : Traversal m => w t.1 x.val.2.val) ht.symm

/-- The source component cost with the actual occurrence matching and its
actual self-links, not a supplied abstract component partition. -/
def cost (c : Component s hs len m cmp err) : ℝ :=
  LinkComponents.componentLabelCost (multiplicity s len m) (P s hs len m cmp err)
    (fun i => (d i : ℝ)) (1/600) s c

theorem root_count
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (w₀ : C → ℤ → Letter) (hcompare₀ : Comparing len m cmp w₀) (hred₀ : Immersed s len w₀)
    (c : Component s hs len m cmp err) :
    ∃ (r : c) (R : Finset (Fin (height s len r.val) → Letter)),
      (R.card : ℝ) ≤ Real.exp (cost s hs len m cmp err d c + (err : ℝ)*Real.log (Fintype.card Letter)) ∧
      ∀ W, Feasible s len m cmp d W → W r.val ∈ R := by
  have halog : 0 ≤ Real.log (Fintype.card Letter) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := Letter))
  by_cases hc : LinkComponents.HasSelf (multiplicity s len m) (P s hs len m cmp err) c
  · obtain ⟨r,tr,hdef,htr⟩ := self_component_translation s hs len m cmp err inverse
      inverse_inverse inverse_ne w₀ hcompare₀ hred₀ hreduced c hc
    refine ⟨r,StageBlocks.translationWords tr,?_,?_⟩
    · have hb : ((StageBlocks.translationWords tr).card : ℝ) ≤
          (Fintype.card Letter : ℝ)^(height s len r.val-tr.domain.card) := by
        exact_mod_cast StageBlocks.translation_card tr
      have ha : 0 < (Fintype.card Letter : ℝ) := by exact_mod_cast Fintype.card_pos
      calc
        _ ≤ (Fintype.card Letter : ℝ)^(height s len r.val-tr.domain.card) := hb
        _ ≤ (Fintype.card Letter : ℝ)^err :=
          pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := Letter)) hdef
        _ = _ := by
          simp only [cost,LinkComponents.componentLabelCost,if_pos hc,zero_add]
          rw [Real.exp_nat_mul,Real.exp_log ha]
    · intro W hW
      obtain ⟨_,w,hw,_,rfl⟩ := hW
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htr Letter inverse w hw⟩
  · let r := LinkComponents.minimumRoot (multiplicity s len m) (P s hs len m cmp err)
      (fun i => (d i : ℝ)) c
    refine ⟨r,binWords (height s len r.val) (d r.val),?_,?_⟩
    · have hb := bin_card_bound (height s len r.val) (hlarge r.val) (d r.val)
      apply hb.trans
      apply Real.exp_le_exp.mpr
      have hh := hscale r.val
      have he := mul_nonneg (Nat.cast_nonneg err : (0:ℝ) ≤ err) halog
      simp only [cost,LinkComponents.componentLabelCost,if_neg hc]
      change 2*(d r.val : ℝ)+2-2*(1/600 : ℝ)*(height s len r.val : ℝ) ≤ _
      linarith
    · intro W hW
      exact hW.1 r.val

/-- Counting the actual stage projection. Self-link roots are selected from
one feasible realization; if none exists, the projection is empty. -/
theorem stage_count (A : Finset (Underlying s len))
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val)) :
    ((StageLabels.stageWords (height s len) A (Feasible s len m cmp d)).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents (L s hs len m cmp err).graph.connectedComponentMk A,
        cost s hs len m cmp err d c.val) +
        2*(err : ℝ)*Fintype.card (Underlying s len)*Real.log (Fintype.card Letter)) := by
  by_cases hex : ∃ W, Feasible s len m cmp d W
  · obtain ⟨W,_,w₀,hw₀,hr₀,_⟩ := hex
    have hroot := root_count s hs len m cmp err d hlarge hscale hreduced w₀ hw₀ hr₀
    choose r R hR hmem using hroot
    exact projection_bound (L s hs len m cmp err) A r R (Feasible s len m cmp d)
      (fun _ hw => feasible_consistent s hs len m cmp err d hw)
      (fun W hw c => hmem c W hw) err
      (links_deficit s hs len m cmp err (symbol len m cmp))
      (cost s hs len m cmp err d) hR
  · rw [projection_empty _ _ _ hex,Finset.card_empty,Nat.cast_zero]
    exact (Real.exp_pos _).le

/-- Stage components are precisely those whose maximum multiplicity exceeds
the zero-based stage number. -/
theorem active_iff (j : ℕ) (c : Component s hs len m cmp err) :
    c ∈ StageLabels.activeComponents (L s hs len m cmp err).graph.connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)) ↔
      j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c := by
  rw [← LinkComponents.active_iff]
  constructor
  · intro hc
    obtain ⟨i,hi,hc⟩ := Finset.mem_image.mp hc
    exact ⟨⟨i,hc⟩,(Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i,hi⟩
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,i.property⟩

/-- Literal source component sum, now in the form used by stage-cost summation. -/
theorem cost_sum (j : ℕ) :
    (∑ c : StageLabels.activeComponents (L s hs len m cmp err).graph.connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)), cost s hs len m cmp err d c.val) =
    ∑ c : Component s hs len m cmp err,
      if j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c then
        cost s hs len m cmp err d c else 0 := by
  change (∑ c : StageLabels.activeComponents
    (LinkComponents.graph (multiplicity s len m) (P s hs len m cmp err)).connectedComponentMk
    (Finset.univ.filter (fun i => j < multiplicity s len m i)), cost s hs len m cmp err d c.val) = _
  rw [Finset.sum_coe_sort]
  have hset : StageLabels.activeComponents
      (LinkComponents.graph (multiplicity s len m) (P s hs len m cmp err)).connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)) =
      Finset.univ.filter (fun c : Component s hs len m cmp err =>
        j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c) := by
    ext c
    exact (active_iff s hs len m cmp err j c).trans (by simp)
  rw [hset,Finset.sum_filter]

end TorsionFreeZeroDivisors.ActualStageLabels

namespace TorsionFreeZeroDivisors.ChainStageLabels
open scoped Classical BigOperators
section
/-- Direct membership in a finite active projection, with the generic index
instances retained rather than recomputed after specializing the sigma type. -/
theorem stageWords_mem {I T : Type*} [Fintype I] [Fintype T] (h : I → ℕ)
    (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop)
    (W : (i : I) → Fin (h i) → T) (hW : P W) :
    (fun i : A => W i.val) ∈ StageLabels.stageWords h A P := by
  apply Finset.mem_image.mpr
  refine ⟨W,?_,rfl⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact hW
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

abbrev ActiveChain := {c : C // j < m c}
abbrev StagePosition := (c : ActiveChain m j) × positions 0 (len c.val)
abbrev StageTail := (c : ActiveChain m j) × tail s (len c.val)
def activeBlocks : Finset (Underlying s len) := Finset.univ.filter (fun i => j < m i.1)

omit [Fintype C] in
include hs in
theorem tail_subset (ell : ℕ) : tail s ell ⊆ positions 0 ell := by
  intro q hq
  obtain ⟨hlo,hhi⟩ := mem_positions.mp hq
  apply mem_positions.mpr
  exact ⟨le_trans (by positivity : (0:ℝ) ≤ (blockCount s ell : ℝ)*s) hlo,hhi⟩

def blockPoint (i : activeBlocks s len m j) (k : Fin (height s len i.val)) :
    StagePosition len m j :=
  ⟨⟨i.val.1,(Finset.mem_filter.mp i.property).2⟩,
    ⟨((wordCoordinate s len i.val).symm k).val,
      full_subset s hs (len i.val.1) i.val.2 ((wordCoordinate s len i.val).symm k).property⟩⟩

def tailPoint (x : StageTail s len m j) : StagePosition len m j :=
  ⟨x.1,⟨x.2.val,tail_subset s hs (len x.1.val) x.2.property⟩⟩

def blockRestrict (F : StagePosition len m j → Letter) :
    (i : activeBlocks s len m j) → Fin (height s len i.val) → Letter :=
  fun i k => F (blockPoint s hs len m j i k)
def tailRestrict (F : StagePosition len m j → Letter) : StageTail s len m j → Letter :=
  fun x => F (tailPoint s hs len m j x)

def encode (F : StagePosition len m j → Letter) :=
  (blockRestrict s hs len m j F,tailRestrict s hs len m j F)

/-- Full blocks and the literal end fragments determine every active chain
letter, without choosing values on inactive chains. -/
theorem encode_injective : Function.Injective (encode s hs len m j) := by
  intro F G he
  have hb := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  funext x
  rcases x with ⟨⟨c,hc⟩,q⟩
  obtain ⟨k,hk⟩ | htq := full_or_tail s hs (len c) q.property
  · let i : activeBlocks s len m j := ⟨⟨c,k⟩,by simp [activeBlocks,hc]⟩
    let z : Fin (height s len i.val) := wordCoordinate s len i.val ⟨q.val,hk⟩
    have h := congr_fun (congr_fun hb i) z
    simpa [encode,blockRestrict,blockPoint,z,i] using h
  · have h := congr_fun ht ⟨⟨c,hc⟩,⟨q.val,htq⟩⟩
    exact h

/-- The exact finite extension factor contributed by arbitrary tail letters. -/
theorem extension_count (X : Finset (StagePosition len m j → Letter))
    (Y : Finset ((i : activeBlocks s len m j) → Fin (height s len i.val) → Letter))
    (hX : ∀ F ∈ X, blockRestrict s hs len m j F ∈ Y) :
    X.card ≤ Y.card * (Fintype.card Letter)^Fintype.card (StageTail s len m j) := by
  calc
    X.card = (X.image (encode s hs len m j)).card :=
      (Finset.card_image_of_injective X (encode_injective s hs len m j)).symm
    _ ≤ (Y ×ˢ Finset.univ).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_product.mpr ⟨hX F hF,Finset.mem_univ _⟩
    _ = _ := by simp

include hs in
/-- The fragment loss is O(s) per marked chain, with a literal uniform bound. -/
theorem tail_count : (Fintype.card (StageTail s len m j) : ℝ) ≤
    (s+1)*Fintype.card C := by
  simp only [StageTail,Fintype.card_sigma,Fintype.card_coe,Nat.cast_sum]
  calc
    (∑ c : ActiveChain m j, ((tail s (len c.val)).card : ℝ)) ≤
        ∑ _c : ActiveChain m j, (s+1) :=
      Finset.sum_le_sum (fun c _ => tail_bound s hs (len c.val))
    _ = (s+1)*Fintype.card (ActiveChain m j) := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Fintype.card_subtype_le (fun c : C => j < m c))
      (by positivity)

variable (cmp : Comparisons (E := E) (traversalLength len m)) (d : Underlying s len → ℤ)

def fullWords : Finset (StagePosition len m j → Letter) :=
  Finset.univ.filter (fun F => ∃ w : C → ℤ → Letter,
    ActualStageLabels.Comparing len m cmp w ∧ ActualStageLabels.Immersed s len w ∧
    (∀ i, word s len w i ∈ binWords (height s len i) (d i)) ∧
    F = fun x => w x.1.val x.2.val)

theorem blockRestrict_word (w : C → ℤ → Letter) :
    blockRestrict s hs len m j (fun x => w x.1.val x.2.val) =
      fun i k => word s len w i.val k := by
  funext i k
  have hv := wordCoordinate_val s len i.val ((wordCoordinate s len i.val).symm k)
  rw [Equiv.apply_symm_apply] at hv
  change w i.val.1 ((wordCoordinate s len i.val).symm k).val =
    w i.val.1 ((k.val : ℤ)+lower s len i.val)
  congr 1
  omega

/-- Every literal feasible full-chain assignment projects to feasible blocks. -/
theorem restrict_mem (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    blockRestrict s hs len m j F ∈ StageLabels.stageWords (height s len)
      (activeBlocks s len m j) (ActualStageLabels.Feasible s len m cmp d) := by
  have hF' : ∃ w : C → ℤ → Letter,
      ActualStageLabels.Comparing len m cmp w ∧ ActualStageLabels.Immersed s len w ∧
      (∀ i, word s len w i ∈ binWords (height s len i) (d i)) ∧
      F = fun x => w x.1.val x.2.val := (Finset.mem_filter.mp hF).2
  obtain ⟨w,hw,hr,hd,rfl⟩ := hF'
  rw [blockRestrict_word]
  have hW : ActualStageLabels.Feasible s len m cmp d (word s len w) := ⟨hd,w,hw,hr,rfl⟩
  exact stageWords_mem (height s len) (activeBlocks s len m j)
    (ActualStageLabels.Feasible s len m cmp d) (word s len w) hW

/-- Numerical extension bound factored independently of the graph types. -/
theorem count_extension_exp (x y k z : ℕ) (cost error bound : ℝ)
    (hxy : x ≤ y*k^z) (hy : (y : ℝ) ≤ Real.exp (cost+error*Real.log k))
    (hz : (z : ℝ) ≤ bound) (hk : 0 < k) :
    (x : ℝ) ≤ Real.exp (cost+(error+bound)*Real.log k) := by
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hpow : (k : ℝ)^z = Real.exp ((z : ℝ)*Real.log k) := by
    rw [Real.exp_nat_mul,Real.exp_log (by exact_mod_cast hk)]
  have hxy' : (x : ℝ) ≤ (y : ℝ)*(k : ℝ)^z := by exact_mod_cast hxy
  calc
    (x : ℝ) ≤ (y : ℝ)*(k : ℝ)^z := hxy'
    _ ≤ Real.exp (cost+error*Real.log k) * (k : ℝ)^z :=
      mul_le_mul_of_nonneg_right hy (by positivity)
    _ = Real.exp (cost+error*Real.log k+(z : ℝ)*Real.log k) := by simp only [hpow,Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hz hlog])

/-- Source stage-label estimate including every tail, not just full blocks. -/
theorem full_stage_count (err : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val)) :
    ((fullWords s len m j cmp d).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents
        (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
        ActualStageLabels.cost s hs len m cmp err d c.val) +
        (2*(err : ℝ)*Fintype.card (Underlying s len)+(s+1)*Fintype.card C)*
          Real.log (Fintype.card Letter)) := by
  have he := extension_count s hs len m j (fullWords s len m j cmp d)
    (StageLabels.stageWords (height s len) (activeBlocks s len m j)
      (ActualStageLabels.Feasible s len m cmp d)) (restrict_mem s hs len m j cmp d)
  have hcard := ActualStageLabels.stage_count s hs len m cmp err d
    (activeBlocks s len m j) hlarge hscale hreduced
  exact count_extension_exp _ _ _ _ _ _ _ he hcard (tail_count s hs len m j)
    (Fintype.card_pos (α := Letter))

end TorsionFreeZeroDivisors.ChainStageLabels

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical
open PortSubdivision
/-- Generic table application avoids reducing the concrete projective-plane
alphabet while composing the elementary cardinality bounds. -/
theorem allowed_turn_table {PV PD TV T : Type*} [Fintype PD] [Fintype TV]
    (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
    (pin : PV → Option TV) (v : PV) (a b : PD)
    (ha : Γ.origin a = v) (hb : Γ.origin b = v)
    (hab : plabel a ≠ plabel b) (f : T → T → ℝ)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤ f t u) :
    ((allowed Γ plabel outgoing pin v).card : ℝ) ≤ f (plabel a) (plabel b) :=
  (Nat.cast_le.mpr (allowed_turn_le Γ plabel outgoing pin v a b ha hb)).trans
    (htable _ _ hab)
end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainRealization
open scoped Classical BigOperators
open ChainSubdivision TorsionFreeZeroDivisors.Types
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V : Type*} [Fintype C] [Fintype V]
variable (len : C → ℕ) (first last : C → V)

/-- A choice of orientation for each actual edge; only this choice, not an
independent matching event for its reverse, is counted. -/
def edgePair (e : Edge len) : Sym2 (Dart len) := s((e,false),(e,true))

omit [Fintype C] [Fintype V] in
theorem edgePair_injective : Function.Injective (edgePair len) := by
  intro e f h
  rw [edgePair,edgePair,Sym2.eq_iff] at h
  rcases h with h | h
  · exact congrArg Prod.fst h.1
  · have hh := congrArg Prod.snd h.1
    cases hh

omit [Fintype V] in
theorem edges_eq : PatternEmbeddings.edges (graph len first last) =
    Finset.univ.image (edgePair len) := by
  ext x
  simp only [PatternEmbeddings.edges,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨e,b⟩,rfl⟩
    refine ⟨e,?_⟩
    cases b
    · rfl
    · exact Sym2.eq_swap
  · rintro ⟨e,rfl⟩
    exact ⟨(e,false),rfl⟩

omit [Fintype V] in
theorem edges_card : (PatternEmbeddings.edges (graph len first last)).card = ∑ c, len c := by
  rw [edges_eq,Finset.card_image_of_injective _ (edgePair_injective len),Finset.card_univ,card_edges]

def label (w : C → ℤ → WordEstimate.Letter) (d : Dart len) : Types.Letter :=
  if d.2 then Types.inverse (signedLetter (w d.1.1 d.1.2.val))
  else signedLetter (w d.1.1 d.1.2.val)

omit [Fintype C] [Fintype V] in
@[simp] theorem label_reverse (w : C → ℤ → WordEstimate.Letter) (d : Dart len) :
    label len w ((graph len first last).reverse d) = Types.inverse (label len w d) := by
  rcases d with ⟨e,b⟩
  cases b <;> simp [label,Types.inverse_inverse]

omit [Fintype C] [Fintype V] in
@[simp] theorem label_back (w : C → ℤ → WordEstimate.Letter) (v : Interior len) :
    label len w (back len v) = Types.inverse (signedLetter (w v.1 v.2.val)) := rfl
omit [Fintype C] [Fintype V] in
@[simp] theorem label_front (w : C → ℤ → WordEstimate.Letter) (v : Interior len) :
    label len w (front len v) = signedLetter (w v.1 ((v.2.val : ℤ)+1)) := by
  simp [label,front,Nat.cast_add]

omit [Fintype C] [Fintype V] in
/-- Literal internal turn weight, not an independent-letter approximation. -/
theorem internal_weight (w : C → ℤ → WordEstimate.Letter)
    (himm : Function.Injective (fun d => ((graph len first last).origin d,label len w d)))
    (v : Interior len) :
    TypeWeights.jointWeight (label len w (back len v)) (label len w (front len v)) =
      WordEstimate.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1)) := by
  have hn : label len w (back len v) ≠ label len w (front len v) := by
    intro he
    exact back_ne_front len v (himm (Prod.ext (by simp) he))
  rw [label_back,label_front] at hn ⊢
  rw [TypeWeights.jointWeight_signed]
  unfold WordEstimate.weight
  split_ifs with he
  · exfalso
    apply hn
    rw [he]
    rcases w v.1 v.2.val with ⟨g,b⟩
    exact Types.inverse_signed g b
  · rfl

def turnProduct (w : C → ℤ → WordEstimate.Letter) : ℝ :=
  ∏ v : Interior len, WordEstimate.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1))

/-- Marked vertices carry the optional prescribed root. Internal vertices
never gain spurious pins. -/
def pin {TV : Type*} (p : V → Option TV) : Vertex len (V := V) → Option TV
  | .inl v => p v
  | .inr _ => none

omit [Fintype C] [Fintype V] in
@[simp] theorem pin_internal {TV : Type*} (p : V → Option TV) (v : Interior len) :
    pin len p (.inr v) = none := rfl

/-- Source vertex-assignment cost, separating the finitely many marked vertices. -/
def cost {TV : Type*} (pp : V → Option TV) (n p : ℝ)
    (w : C → ℤ → WordEstimate.Letter) : Vertex len (V := V) → ℝ
  | .inl v => if pp v = none then n else 1
  | .inr v => n*p*WordEstimate.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1))

theorem cost_product {TV : Type*} (pp : V → Option TV) (n p : ℝ)
    (w : C → ℤ → WordEstimate.Letter) :
    (∏ v, cost len pp n p w v) =
      n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
        p^(∑ c, (len c-1)) * turnProduct len w := by
  rw [Fintype.prod_sum_type]
  simp only [cost,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    card_interiors,Finset.prod_ite,Finset.prod_const,one_pow,mul_one,pow_add,
    turnProduct]
  ring

omit [Fintype V] in
theorem allowed_cost {TV : Type*} [Fintype TV]
    (outgoing : TV → Finset Types.Letter) (pp : V → Option TV)
    (n p : ℝ) (w : C → ℤ → WordEstimate.Letter)
    (himm : Function.Injective (fun d => ((graph len first last).origin d,label len w d)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤
        n*p*TypeWeights.jointWeight t u) :
    ∀ v, ((StageRealization.allowed (graph len first last) (label len w)
      outgoing (pin len pp) v).card : ℝ) ≤ cost len pp n p w v := by
  intro v
  cases v with
  | inl v =>
    dsimp [cost]
    split_ifs with hp
    · exact (Nat.cast_le.mpr (StageRealization.allowed_card_le _ _ _ _ _)).trans hn
    · obtain ⟨x,hx⟩ := Option.ne_none_iff_exists'.mp hp
      exact_mod_cast StageRealization.pinned_card_le (graph len first last)
        (label len w) outgoing (pin len pp) (.inl v) x hx
  | inr v =>

    have hn' : label len w (back len v) ≠ label len w (front len v) := by
      intro he
      exact back_ne_front len v (himm (Prod.ext (by simp) he))
    have h := StageRealization.allowed_turn_table (graph len first last) (label len w)
      outgoing (pin len pp) (.inr v) (back len v) (front len v)
      (back_origin len first last v) (front_origin len first last v) hn'
      (fun t u => n*p*TypeWeights.jointWeight t u) (by
        intro t u htu
        simpa only [← Nat.card_eq_fintype_card] using htable t u htu)
    rwa [internal_weight len first last w himm] at h

/-- Exact finite first moment for an actually subdivided chain pattern. The
fixed root costs one instead of n; all unmarked vertices use the type table. -/
theorem fixed_label_bound {TV : Type*} [Fintype TV]
    (outgoing : TV → Finset Types.Letter) (pp : V → Option TV)
    (n p : ℝ) (w : C → ℤ → WordEstimate.Letter)
    (himm : Function.Injective (fun d => ((graph len first last).origin d,label len w d)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤
        n*p*TypeWeights.jointWeight t u)
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : PatternEmbeddings.Dart outgoing //
      PatternEmbeddings.origin outgoing e = v} ≤ d)
    (hsize : ∀ x : PatternEmbeddings.Dart outgoing,
      R + (∑ c, len c) + 4*d^(2*N+1) ≤
        Nat.card {e : PatternEmbeddings.Dart outgoing //
          PatternEmbeddings.label outgoing e = PatternEmbeddings.label outgoing x})
    (hΩ : (ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅).Nonempty) :
    ((∑ r ∈ ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅,
        StageRealization.realizations (graph len first last) (label len w) outgoing
          (pin len pp) Types.inverse r : ℕ) : ℝ) /
        (ConditionedMatchings.Matching.conditioned
          (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
          (PatternEmbeddings.origin outgoing) N ∅).card ≤
      (n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
        p^(∑ c, (len c-1)) * turnProduct len w) / (R : ℝ)^(∑ c, len c) := by
  have h := StageRealization.fixed_label_bound (graph len first last) (label len w)
    outgoing (pin len pp) Types.inverse Types.inverse_ne himm N d R h2 hR hd
    (by intro x; rw [edges_card]; exact hsize x) hΩ (cost len pp n p w)
    (allowed_cost len first last outgoing pp n p w himm hn htable)
  rwa [cost_product,edges_card] at h

end TorsionFreeZeroDivisors.ChainRealization

namespace TorsionFreeZeroDivisors.ChainWeights
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len : C → ℕ)

abbrev BlockTurn := (i : Underlying s len) × Fin (height s len i-1)

def firstCoordinate (i : Underlying s len) (k : Fin (height s len i-1)) : block s i.2.val :=
  (wordCoordinate s len i).symm ⟨k.val,by omega⟩
def nextCoordinate (i : Underlying s len) (k : Fin (height s len i-1)) : block s i.2.val :=
  (wordCoordinate s len i).symm ⟨k.val+1,by omega⟩

omit [Fintype C] in
@[simp] theorem firstCoordinate_val (i : Underlying s len) (k : Fin (height s len i-1)) :
    (firstCoordinate s len i k).val = (k.val : ℤ)+lower s len i := by
  have h := wordCoordinate_val s len i (firstCoordinate s len i k)
  simp only [firstCoordinate,Equiv.apply_symm_apply] at h
  dsimp only [firstCoordinate]
  omega
omit [Fintype C] in
@[simp] theorem nextCoordinate_val (i : Underlying s len) (k : Fin (height s len i-1)) :
    (nextCoordinate s len i k).val = (k.val : ℤ)+lower s len i+1 := by
  have h := wordCoordinate_val s len i (nextCoordinate s len i k)
  simp only [nextCoordinate,Equiv.apply_symm_apply,Nat.cast_add,Nat.cast_one] at h
  dsimp only [nextCoordinate]
  omega

def turnPoint (x : BlockTurn s len) : Position len :=
  includeBlock s hs len x.1 (firstCoordinate s len x.1 x.2)

def turns : Finset (Position len) := Finset.univ.filter (fun x => x.2.val+1 ∈ positions 0 (len x.1))

theorem turnPoint_mem (x : BlockTurn s len) : turnPoint s hs len x ∈ turns len := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have ht := full_subset s hs (len x.1.1) x.1.2 (nextCoordinate s len x.1 x.2).property
  change (firstCoordinate s len x.1 x.2).val+1 ∈ positions 0 (len x.1.1)
  simpa only [firstCoordinate_val,nextCoordinate_val] using ht

omit [Fintype C] in
theorem turnPoint_block (x : BlockTurn s len) :
    turnPoint s hs len x ∈ blockPositions s hs len x.1 := by
  exact Finset.mem_map.mpr ⟨firstCoordinate s len x.1 x.2,Finset.mem_attach _ _,rfl⟩

omit [Fintype C] in
/-- Different block turns are different turns of the actual chain subdivision. -/
theorem turnPoint_injective : Function.Injective (turnPoint s hs len) := by
  intro x y he
  have hc : x.1 = y.1 := by
    by_contra hn
    exact Finset.disjoint_left.mp (blockPositions_disjoint s hs len hn)
      (turnPoint_block s hs len x) (he ▸ turnPoint_block s hs len y)
  rcases x with ⟨i,k⟩
  rcases y with ⟨i',l⟩
  dsimp at hc
  subst i'
  have hv := congrArg (fun x : Position len => x.2.val) he
  change (firstCoordinate s len i k).val = (firstCoordinate s len i l).val at hv
  rw [firstCoordinate_val,firstCoordinate_val] at hv
  have hk : k = l := Fin.ext (by omega)
  cases hk
  rfl

def atTurn (w : C → ℤ → Letter) (x : Position len) : ℝ :=
  weight (w x.1 x.2.val) (w x.1 (x.2.val+1))
def chainProduct (w : C → ℤ → Letter) : ℝ := ∏ x ∈ turns len, atTurn len w x

omit [Fintype C] in
theorem wordWeight_pred (h : ℕ) (W : Fin h → Letter) :
    wordWeight h W = ∏ k : Fin (h-1), weight (W ⟨k.val,by omega⟩) (W ⟨k.val+1,by omega⟩) := by
  cases h with
  | zero => simp [wordWeight]
  | succ h => exact wordWeight_eq_product h W

theorem turn_product (w : C → ℤ → Letter) :
    (∏ x : BlockTurn s len, atTurn len w (turnPoint s hs len x)) =
      ∏ i : Underlying s len, wordWeight (height s len i) (word s len w i) := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [wordWeight_pred]
  apply Finset.prod_congr rfl
  intro k _
  change weight (w i.1 (firstCoordinate s len i k).val)
    (w i.1 ((firstCoordinate s len i k).val+1)) =
    weight (w i.1 ((k.val : ℤ)+lower s len i))
      (w i.1 (((k.val+1 : ℕ) : ℤ)+lower s len i))
  rw [firstCoordinate_val]
  simp only [Nat.cast_add,Nat.cast_one]
  congr 2; ring

include hs in
/-- Discarding only nonnegative factors at most one can increase a chain's
turn product. This accounts for cross-block turns and all end fragments. -/
theorem chain_le_blocks (w : C → ℤ → Letter) :
    chainProduct len w ≤ ∏ i : Underlying s len, wordWeight (height s len i) (word s len w i) := by
  let S := Finset.univ.image (turnPoint s hs len)
  have hS : S ⊆ turns len := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact turnPoint_mem s hs len y
  calc
    chainProduct len w ≤ ∏ x ∈ S, atTurn len w x :=
      Finset.prod_le_prod_of_subset_of_le_one hS (fun x _ => weight_nonneg _ _)
        (fun x _ _ => weight_le_one _ _)
    _ = ∏ x : BlockTurn s len, atTurn len w (turnPoint s hs len x) := by
      exact Finset.prod_image (fun _ _ _ _ he => turnPoint_injective s hs len he)
    _ = _ := turn_product s hs len w

/-- A literal bin contributes its upper endpoint to the fixed-label exponent. -/
theorem bin_weight_upper {h : ℕ} {d : ℤ} {W : Fin h → Letter}
    (hW : W ∈ binWords h d) : wordWeight h W ≤ Real.exp (-(d : ℝ)) := by
  obtain ⟨hp,he⟩ := (Finset.mem_filter.mp hW).2
  have hf := Int.floor_le (-Real.log (wordWeight h W))
  rw [he] at hf
  calc
    wordWeight h W = Real.exp (Real.log (wordWeight h W)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

include hs in
/-- Fixed-label loss from all active full blocks. The stage instance is
obtained by taking C to be the active-chain subtype itself. -/
theorem chain_bin_bound (w : C → ℤ → Letter) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ binWords (height s len i) (d i)) :
    chainProduct len w ≤ Real.exp (-∑ i, (d i : ℝ)) := by
  refine (chain_le_blocks s hs len w).trans ?_
  calc
    (∏ i, wordWeight (height s len i) (word s len w i)) ≤ ∏ i, Real.exp (-(d i : ℝ)) :=
      Finset.prod_le_prod (fun i _ => wordWeight_nonneg _ _) (fun i _ => bin_weight_upper (hbin i))
    _ = _ := by rw [← Real.exp_sum,Finset.sum_neg_distrib]

omit [Fintype C] in
theorem mem_positions_nat (n : ℕ) (q : ℤ) :
    q ∈ positions 0 n ↔ 0 ≤ q ∧ q < n := by
  have hlo : ⌈(0 : ℝ)-1/2⌉ = (0 : ℤ) := by norm_num
  have hhi : ⌈(n : ℝ)-1/2⌉ = (n : ℤ) := by
    apply Int.ceil_eq_iff.mpr
    push_cast
    constructor <;> linarith
  simp only [positions,hlo,hhi,Finset.mem_Ico]

/-- Literal indexing equivalence from internal subdivision vertices to the
half-integer-grid turn positions. -/
def turnEquiv : ((c : C) × Fin (len c-1)) ≃ (turns len) where
  toFun v := ⟨⟨v.1,⟨(v.2.val : ℤ),(mem_positions_nat (len v.1) v.2.val).mpr
      ⟨by omega,by omega⟩⟩⟩,by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (mem_positions_nat (len v.1) (v.2.val+1)).mpr
      ⟨by omega,by omega⟩⟩⟩
  invFun x := ⟨x.val.1,⟨x.val.2.val.toNat,by
    have h0 := (mem_positions_nat (len x.val.1) x.val.2.val).mp x.val.2.property
    have h1 := (mem_positions_nat (len x.val.1) (x.val.2.val+1)).mp
      (Finset.mem_filter.mp x.property).2
    omega⟩⟩
  left_inv v := by
    rcases v with ⟨c,k⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Fin.ext
    exact Int.toNat_natCast k.val
  right_inv x := by
    rcases x with ⟨⟨c,q,hq⟩,hx⟩
    apply Subtype.ext
    dsimp only
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    exact Int.toNat_of_nonneg ((mem_positions_nat _ _).mp hq).1

/-- The full-chain product is exactly the product over the actual internal
vertices used in the matching first moment. -/
theorem chainProduct_eq (w : C → ℤ → Letter) :
    chainProduct len w = ∏ v : ((c : C) × Fin (len c-1)),
      weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ)+1)) := by
  rw [chainProduct,← Finset.prod_coe_sort]
  symm
  exact Fintype.prod_equiv (turnEquiv len) _ _ (fun _ => rfl)

end TorsionFreeZeroDivisors.ChainWeights

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageExpectation
open scoped Classical BigOperators
open ChainSubdivision BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
section
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

include hs in
/-- The retained full-block bins bound the actual turn product of the
subdivided graph, not a separate abstract word process. -/
theorem turnProduct_bin (w : C → ℤ → Letter) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ binWords (height s len i) (d i)) :
    ChainRealization.turnProduct len w ≤ Real.exp (-∑ i, (d i : ℝ)) := by
  rw [ChainRealization.turnProduct,← ChainWeights.chainProduct_eq len w]
  exact ChainWeights.chain_bin_bound s hs len w d hbin

include hs in
/-- Source equation (entropy-fixed-label-expectation), in its exact finite
form before the uniform asymptotic prescription and marked-vertex errors. -/
theorem fixed_label_bin_bound (outgoing : TV → Finset Types.Letter)
    (pp : V → Option TV) (n p : ℝ) (hp : 0 ≤ p)
    (w : C → ℤ → Letter) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ binWords (height s len i) (d i))
    (himm : Function.Injective (fun a =>
      ((graph len first last).origin a, ChainRealization.label len w a)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤
        n*p*TypeWeights.jointWeight t u)
    (N D R : ℕ) (hD : 2 ≤ D) (hR : 0 < R)
    (hdegree : ∀ v, Nat.card {a : PatternEmbeddings.Dart outgoing //
      PatternEmbeddings.origin outgoing a = v} ≤ D)
    (hsize : ∀ x : PatternEmbeddings.Dart outgoing,
      R + (∑ c, len c) + 4*D^(2*N+1) ≤
        Nat.card {a : PatternEmbeddings.Dart outgoing //
          PatternEmbeddings.label outgoing a = PatternEmbeddings.label outgoing x})
    (hΩ : (ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅).Nonempty) :
    ((∑ r ∈ ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅,
        StageRealization.realizations (graph len first last) (ChainRealization.label len w)
          outgoing (ChainRealization.pin len pp) Types.inverse r : ℕ) : ℝ) /
      (ConditionedMatchings.Matching.conditioned
        (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
        (PatternEmbeddings.origin outgoing) N ∅).card ≤
      (n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
        p^(∑ c, (len c-1))) / (R : ℝ)^(∑ c, len c) *
        Real.exp (-∑ i, (d i : ℝ)) := by
  have hn0 : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TV)).trans hn
  refine (ChainRealization.fixed_label_bound len first last outgoing pp n p w
    himm hn htable N D R hD hR hdegree hsize hΩ).trans ?_
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (turnProduct_bin s hs len w d hbin) (by positivity)

/-- Finite letters on a chain, extended only to make the integer indexing
convenient. The fallback is never used at an edge of the pattern. -/
def readWord (F : ComparedBlocks.Position len → Letter) (c : C) (q : ℤ) : Letter :=
  if h : q ∈ positions 0 (len c) then F ⟨c,⟨q,h⟩⟩ else default

omit [Fintype C] in
@[simp] theorem readWord_on (F : ComparedBlocks.Position len → Letter) (c : C)
    (q : positions 0 (len c)) : readWord len F c q.val = F ⟨c,q⟩ := by
  simp [readWord,q.property]

omit [Fintype C] in
include hs in
theorem word_position (i : Underlying s len) (k : Fin (height s len i)) :
    (k.val : ℤ)+lower s len i ∈ positions 0 (len i.1) := by
  let q := (wordCoordinate s len i).symm k
  have hv := wordCoordinate_val s len i q
  rw [show (wordCoordinate s len i) q = k from Equiv.apply_symm_apply _ _] at hv
  have he : (k.val : ℤ)+lower s len i = q.val := by omega
  rw [he]
  exact full_subset s hs (len i.1) i.2 q.property

end

section Active
open ChainStageLabels
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

abbrev activeLen : ActiveChain m j → ℕ := fun c => len c.val

def activeIndex (i : Underlying s (activeLen len m j)) : Underlying s len := ⟨i.1.val,i.2⟩

/-- The active-block subtype counts exactly the full blocks of the active
chains; no inactive full block is inserted into this stage. -/
def activeBlockEquiv : Underlying s (activeLen len m j) ≃ activeBlocks s len m j where
  toFun i := ⟨activeIndex s len m j i,by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.1.property⟩⟩
  invFun i := ⟨⟨i.val.1,(Finset.mem_filter.mp i.property).2⟩,i.val.2⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

/-- Equality of the literal active bin sum and the filtered global bin sum. -/
theorem active_bin_sum (d : Underlying s len → ℤ) :
    (∑ i : Underlying s (activeLen len m j), (d (activeIndex s len m j i) : ℝ)) =
      ∑ i ∈ activeBlocks s len m j, (d i : ℝ) := by
  calc
    _ = ∑ i : activeBlocks s len m j, (d i.val : ℝ) :=
      Fintype.sum_equiv (activeBlockEquiv s len m j) _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort (activeBlocks s len m j) (fun i => (d i : ℝ))

end Active
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)
local instance : DecidableEq Types.Letter := Classical.decEq _

end TorsionFreeZeroDivisors.StageExpectation

/-! Finite Fubini for the product of the separately girth-conditioned sides.
The label set here is global: it is not replaced by the product of its two
projections. This is the independence actually used in entropy.tex 396–435. -/
namespace TorsionFreeZeroDivisors.TwoSideMean
open scoped BigOperators Classical

variable {A B W : Type*}

def mean (Ω : Finset A) (X : A → ℕ) : ℝ := (∑ r ∈ Ω, X r : ℕ) / (Ω.card : ℝ)

theorem mean_nonneg (Ω : Finset A) (X : A → ℕ) : 0 ≤ mean Ω X := by
  unfold mean
  positivity

theorem mean_product (ΩA : Finset A) (ΩB : Finset B) (X : A → ℕ) (Y : B → ℕ) :
    mean (ΩA ×ˢ ΩB) (fun r => X r.1 * Y r.2) = mean ΩA X * mean ΩB Y := by
  unfold mean
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, Finset.card_product, Nat.cast_mul, Nat.cast_mul]
  ring

/-- The product model factors only after a whole global label assignment is
fixed. No assertion that the allowed labels on the two sides are independent. -/
theorem fixed_mean_bound (ΩA : Finset A) (ΩB : Finset B)
    (X : A → ℕ) (Y : B → ℕ) {a b : ℝ}
    (ha : mean ΩA X ≤ a) (hb : mean ΩB Y ≤ b) :
    mean (ΩA ×ˢ ΩB) (fun r => X r.1 * Y r.2) ≤ a*b := by
  rw [mean_product]
  exact mul_le_mul ha hb (mean_nonneg ΩB Y) ((mean_nonneg ΩA X).trans ha)

/-- A finite union bound keeps the exact number of global label assignments,
not a product of the sizes of projection sets (which could lose the entropy). -/
theorem label_union (Ω : Finset A) (labels : Finset W) (X : W → A → ℕ)
    {b : ℝ} (hX : ∀ w ∈ labels, mean Ω (X w) ≤ b) :
    mean Ω (fun r => ∑ w ∈ labels, X w r) ≤ (labels.card : ℝ)*b := by
  unfold mean at *
  rw [Finset.sum_comm, Nat.cast_sum, Finset.sum_div]
  calc
    _ ≤ ∑ _w ∈ labels, b := Finset.sum_le_sum hX
    _ = _ := by simp

theorem global_mean_bound (ΩA : Finset A) (ΩB : Finset B) (labels : Finset W)
    (X : W → A → ℕ) (Y : W → B → ℕ) {a b : ℝ}
    (ha : ∀ w ∈ labels, mean ΩA (X w) ≤ a)
    (hb : ∀ w ∈ labels, mean ΩB (Y w) ≤ b) :
    mean (ΩA ×ˢ ΩB) (fun r => ∑ w ∈ labels, X w r.1 * Y w r.2) ≤
      (labels.card : ℝ)*(a*b) := by
  exact label_union _ _ _ fun w hw => fixed_mean_bound _ _ _ _ (ha w hw) (hb w hw)

end TorsionFreeZeroDivisors.TwoSideMean

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
open ChainSubdivision PatternEmbeddings ConditionedMatchings BlockAlignment ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

/-- A stage on one prescribed side. Its marked vertices do not include any
isolated vertices of inactive chains. The source number of available vertices
is n on EACH side, not the cardinality 2n of their disjoint union. -/
structure Side where
  C : Type
  V : Type
  TV : Type
  fC : Fintype C
  fV : Fintype V
  fTV : Fintype TV
  len : C → ℕ
  first : C → V
  last : C → V
  outgoing : TV → Finset Types.Letter
  pin : V → Option TV
attribute [instance] Side.fC Side.fV Side.fTV

abbrev Side.Word (S : Side) := ComparedBlocks.Position S.len → WordEstimate.Letter
abbrev Side.Match (S : Side) := Matching (label S.outgoing) Types.inverse

def Side.samples (S : Side) (N : ℕ) : Finset S.Match :=
  Matching.conditioned (label := label S.outgoing) (bar := Types.inverse)
    (origin S.outgoing) N ∅

def Side.immersed (S : Side) (F : S.Word) : Prop :=
  Function.Injective (fun a => ((graph S.len S.first S.last).origin a,
    ChainRealization.label S.len (StageExpectation.readWord S.len F) a))

def Side.realizations (S : Side) (F : S.Word) (r : S.Match) : ℕ :=
  StageRealization.realizations (graph S.len S.first S.last)
    (ChainRealization.label S.len (StageExpectation.readWord S.len F))
    S.outgoing (ChainRealization.pin S.len S.pin) Types.inverse r

def Side.internal (S : Side) : ℕ := ∑ c, (S.len c-1)
def Side.edges (S : Side) : ℕ := ∑ c, S.len c
def Side.freeMarks (S : Side) : ℕ := (Finset.univ.filter fun v => S.pin v = none).card

def Side.cost (S : Side) (n p : ℝ) (R : ℕ) : ℝ :=
  (n^(S.freeMarks+S.internal)*p^S.internal)/(R : ℝ)^S.edges

/-- All probability hypotheses are the literal finite matching conditions.
No expected count or entropy estimate is a field of this certificate. -/
structure Conditions (S : Side) (n p : ℝ) (N D R : ℕ) : Prop where
  nonneg : 0 ≤ p
  vertices : (Fintype.card S.TV : ℝ) ≤ n
  table : ∀ t u, t ≠ u →
    (Fintype.card {x : S.TV // t ∈ S.outgoing x ∧ u ∈ S.outgoing x} : ℝ) ≤
      n*p*TypeWeights.jointWeight t u
  degree_lower : 2 ≤ D
  denominator_pos : 0 < R
  degree : ∀ v, Nat.card {a : PatternEmbeddings.Dart S.outgoing // origin S.outgoing a = v} ≤ D
  room : ∀ x : PatternEmbeddings.Dart S.outgoing,
    R+S.edges+4*D^(2*N+1) ≤
      Nat.card {a : PatternEmbeddings.Dart S.outgoing // label S.outgoing a = label S.outgoing x}
  nonempty : (S.samples N).Nonempty

variable (s : ℝ) (hs : 0 < s)

def Side.bins (S : Side) (d : Underlying s S.len → ℤ) (F : S.Word) : Prop :=
  ∀ i, RepeatedBlocks.word s S.len (StageExpectation.readWord S.len F) i ∈
    WordEstimate.binWords (RepeatedBlocks.height s S.len i) (d i)

include hs in
/-- Exact single-side specialization reused at each fixed GLOBAL label. -/
theorem fixed_mean (S : Side) (n p : ℝ) (N D R : ℕ) (h : Conditions S n p N D R)
    (F : S.Word) (hF : S.immersed F) (d : Underlying s S.len → ℤ)
    (hd : S.bins s d F) :
    TwoSideMean.mean (S.samples N) (S.realizations F) ≤
      S.cost n p R * Real.exp (-∑ i, (d i : ℝ)) := by
  exact StageExpectation.fixed_label_bin_bound s hs S.len S.first S.last S.outgoing S.pin
    n p h.nonneg (StageExpectation.readWord S.len F) d hd hF h.vertices h.table
    N D R h.degree_lower h.denominator_pos h.degree h.room h.nonempty

variable {W : Type*}

/-- Only one filter of the global string set; it does not discard comparisons
between sides or enlarge that set to the product of projections. -/
def immersedLabels (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word) : Finset W :=
  X.filter fun w => A.immersed (WA w) ∧ B.immersed (WB w)

def count (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (r : A.Match × B.Match) : ℕ :=
  ∑ w ∈ immersedLabels A B X WA WB, A.realizations (WA w) r.1 * B.realizations (WB w) r.2

include hs in
/-- Literal two-side stage first moment. Conditioning factors into the product
of the girth restrictions; repeated-edge dependencies stay inside each matching. -/
theorem mean_bound (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (n p : ℝ) (N D R : ℕ) (hA : Conditions A n p N D R) (hB : Conditions B n p N D R)
    (dA : Underlying s A.len → ℤ) (dB : Underlying s B.len → ℤ)
    (hdA : ∀ w ∈ X, A.bins s dA (WA w)) (hdB : ∀ w ∈ X, B.bins s dB (WB w)) :
    TwoSideMean.mean ((A.samples N) ×ˢ (B.samples N)) (count A B X WA WB) ≤
      (X.card : ℝ)*((A.cost n p R * B.cost n p R) *
        Real.exp (-(∑ i, (dA i : ℝ))-(∑ i, (dB i : ℝ)))) := by
  have hn : 0 ≤ n := (Nat.cast_nonneg (Fintype.card A.TV)).trans hA.vertices
  have hp := hA.nonneg
  have hcost : 0 ≤ (A.cost n p R * B.cost n p R) *
      Real.exp (-(∑ i, (dA i : ℝ))-(∑ i, (dB i : ℝ))) := by
    unfold Side.cost
    positivity
  have he := TwoSideMean.global_mean_bound (A.samples N) (B.samples N)
    (immersedLabels A B X WA WB) (fun w => A.realizations (WA w)) (fun w => B.realizations (WB w))
    (fun w hw => fixed_mean s hs A n p N D R hA (WA w)
      (Finset.mem_filter.mp hw).2.1 dA (hdA w (Finset.mem_filter.mp hw).1))
    (fun w hw => fixed_mean s hs B n p N D R hB (WB w)
      (Finset.mem_filter.mp hw).2.2 dB (hdB w (Finset.mem_filter.mp hw).1))
  have eq : (A.cost n p R * Real.exp (-∑ i, (dA i : ℝ))) *
      (B.cost n p R * Real.exp (-∑ i, (dB i : ℝ))) =
      (A.cost n p R * B.cost n p R)*
        Real.exp (-(∑ i, (dA i : ℝ))-(∑ i, (dB i : ℝ))) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [eq] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Finset.card_filter_le ..)) hcost)

/-- No entropy factor 2 is introduced when the two sides are combined. -/
theorem cost_product (A B : Side) (n p : ℝ) (R : ℕ) :
    A.cost n p R * B.cost n p R =
      (n^(A.freeMarks+A.internal+B.freeMarks+B.internal) * p^(A.internal+B.internal)) /
        (R : ℝ)^(A.edges+B.edges) := by
  simp only [Side.cost, pow_add]
  ring

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TwoSideFullStage
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks ChainStageLabels WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)

variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.TwoSideFullStage

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

/-- Nonemptiness of the exact typed matching family conditioned on girth.
The numerical hypothesis is an explicit finite-size bound, not a new standing
hypothesis for the main existential theorem. -/
theorem exists_typed_large_girth (origin : D → V) (label : D → T) (bar : T → T)
    (Γ₀ : PortGraph V D) (ho : Γ₀.origin = origin)
    (hlabel : ∀ f, label (Γ₀.reverse f) = bar (label f))
    (d N : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (hbig : ∀ x, 4*d^(2*N+1) < Nat.card {e : D // label e = label x}) :
    ∃ Γ : PortGraph V D, Γ.origin = origin ∧
      (∀ f, label (Γ.reverse f) = bar (label f)) ∧
      (N : ℕ∞) ≤ Γ.subdivision.egirth := by
  classical
  let P : SimpleGraph (V ⊕ D) → Prop := fun G =>
    ∃ Γ : PortGraph V D, Γ.origin = origin ∧
      (∀ f, label (Γ.reverse f) = bar (label f)) ∧ G = Γ.subdivision
  have hne : ∃ G, P G := ⟨Γ₀.subdivision,Γ₀,ho,hlabel,rfl⟩
  have hsw : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set (V ⊕ D)), ∀ b ∈ ({u,z} : Set (V ⊕ D)),
          ∀ p : G.Walk a b, 2*N < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y) := by
    rintro G ⟨Γ,hΓo,hΓl,rfl⟩ a p hp
    obtain ⟨x,hx⟩ := Γ.cycle_has_middle p hp
    have hd' : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d := by rw [hΓo]; exact hd
    obtain ⟨e,hel,hfar⟩ := exists_far_port Γ label d (2*N) h2 hd' x (hbig x)
    have hxe : x ≠ e := by
      intro h
      have hf := hfar (.inr x) (by simp) (.inr e) (by simp)
      subst e
      have hh := hf SimpleGraph.Walk.nil
      simp at hh
    have hxr : x ≠ Γ.reverse e := by
      intro h
      have hf := hfar (.inr x) (by simp) (.inr (Γ.reverse e)) (by simp)
      rw [h] at hf
      have hh := hf SimpleGraph.Walk.nil
      simp at hh
    refine ⟨.inr x,.inr (Γ.reverse x),.inr e,.inr (Γ.reverse e),hx,rfl,hfar,?_⟩
    refine ⟨Γ.switch x e,hΓo,Γ.switch_preserves_labels label bar hΓl x e hel.symm,?_⟩
    exact (subdivision_switch Γ x e hxe hxr).symm
  obtain ⟨G,⟨Γ,hΓo,hΓl,hG⟩,hg⟩ := exists_large_girth N P hne hsw
  exact ⟨Γ,hΓo,hΓl,hG ▸ hg⟩

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.TypedGraphs
open TorsionFreeZeroDivisors.Types PortSubdivision ConditionedMatchings MatchingGraphs
variable {V : Type*} (outgoing : V → Finset Letter)

def reverse (M : MatchingTuple outgoing) (e : Dart outgoing) : Dart outgoing :=
  ⟨(next outgoing M e.val.1 e.val.2,inverse e.val.2),
    next_reverse_mem outgoing M e.val.1 e.val.2 e.property⟩

theorem reverse_involutive (M : MatchingTuple outgoing) :
    Function.Involutive (reverse outgoing M) := by
  intro e
  apply Subtype.ext
  exact Prod.ext (next_reverse_next outgoing M e.val.1 e.val.2 e.property)
    (inverse_inverse e.val.2)

def matching (M : MatchingTuple outgoing) : Matching (label outgoing) inverse :=
  ⟨(reverse_involutive outgoing M).toPerm (reverse outgoing M),
    reverse_involutive outgoing M,by
      intro e he
      exact inverse_ne e.val.2 (congrArg (label outgoing) he),fun _ => rfl⟩

/-- An origin fibre is exactly the prescribed outgoing type. -/
def originFiber (v : V) : {e : Dart outgoing // origin outgoing e = v} ≃
    {t : Letter // t ∈ outgoing v} where
  toFun e := ⟨e.val.val.2,by
    have h := e.val.property
    simpa only [← e.property,origin,label] using h⟩
  invFun t := ⟨⟨(v,t.val),t.property⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.property.symm rfl
  right_inv _ := rfl

/-- A letter fibre is exactly its empirical carrier set on this side. -/
def labelFiber (t : Letter) : {e : Dart outgoing // label outgoing e = t} ≃
    {v : V // t ∈ outgoing v} where
  toFun e := ⟨e.val.val.1,by
    have h := e.val.property
    simpa only [← e.property,origin,label] using h⟩
  invFun v := ⟨⟨(v.val,t),v.property⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl e.property.symm
  right_inv _ := rfl

theorem origin_card (v : V) :
    Nat.card {e : Dart outgoing // origin outgoing e = v} = (outgoing v).card := by
  rw [Nat.card_congr (originFiber outgoing v), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem label_card [Fintype V] (t : Letter) :
    Nat.card {e : Dart outgoing // label outgoing e = t} =
      Fintype.card {v : V // t ∈ outgoing v} := by
  rw [Nat.card_congr (labelFiber outgoing t),Nat.card_eq_fintype_card]

theorem exists_conditioned [Fintype V] (M : MatchingTuple outgoing) (N : ℕ)
    (hd : ∀ v, (outgoing v).card ≤ 132)
    (hsize : ∀ t, 4*132^(2*N+1) < Fintype.card {v : V // t ∈ outgoing v}) :
    (Matching.conditioned (label := label outgoing) (bar := inverse)
      (origin outgoing) N ∅).Nonempty := by
  classical
  let r := matching outgoing M
  obtain ⟨Γ,hΓo,hΓl,hg⟩ := exists_typed_large_girth
    (origin outgoing) (label outgoing) inverse (r.graph (origin outgoing)) rfl
    (fun e => r.label_reverse e) 132 N (by norm_num)
    (fun v => by rw [origin_card]; exact hd v)
    (fun e => by rw [label_card]; exact hsize _)
  let r' : Matching (label outgoing) inverse :=
    ⟨Γ.reverse_reverse.toPerm Γ.reverse,Γ.reverse_reverse,Γ.reverse_ne,hΓl⟩
  refine ⟨r',Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩⟩
  · intro a b h
    exact False.elim (Finset.notMem_empty _ h)
  · have he : r'.graph (origin outgoing) = Γ := by
      cases Γ
      simp_all only [Matching.graph]
      rfl
    rw [he]
    exact hg

/-- The actual prescribed A-side graph space has nonzero cardinality. -/
theorem conditionedA_nonempty (rep N : ℕ) (hsize : 4*132^(2*N+1) < 4260354*rep) :
    (Matching.conditioned (label := label (@outgoingA rep)) (bar := inverse)
      (origin (@outgoingA rep)) N ∅).Nonempty := by
  classical
  exact exists_conditioned _ (Classical.choice (matchingA_nonempty rep)) N
    (fun v => (degreeA_bounds v).2)
    (fun t => by rw [letter_frequencyA]; exact hsize)

theorem conditionedB_nonempty (rep N : ℕ) (hsize : 4*132^(2*N+1) < 4260354*rep) :
    (Matching.conditioned (label := label (@outgoingB rep)) (bar := inverse)
      (origin (@outgoingB rep)) N ∅).Nonempty := by
  classical
  exact exists_conditioned _ (Classical.choice (matchingB_nonempty rep)) N
    (fun v => (degreeB_bounds v).2)
    (fun t => by rw [letter_frequencyB]; exact hsize)

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.GirthAsymptotics
open Filter
open scoped Topology

end TorsionFreeZeroDivisors.GirthAsymptotics

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedGraphs
open Filter GirthAsymptotics TorsionFreeZeroDivisors.Types ConditionedMatchings PortSubdivision
open scoped Topology

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.TypedStage
open scoped Classical BigOperators Topology
open TorsionFreeZeroDivisors.Types TwoSideStage GirthAsymptotics Filter
local instance : DecidableEq Types.Letter := Classical.decEq _

variable {C V : Type} [Fintype C] [Fintype V]
variable (rep : ℕ) (len : C → ℕ) (first last : C → V)

abbrev sideA (pin : V → Option (VertexA rep)) : TwoSideStage.Side where
  C := C
  V := V
  TV := VertexA rep
  fC := inferInstance
  fV := inferInstance
  fTV := inferInstance
  len := len
  first := first
  last := last
  outgoing := @outgoingA rep
  pin := pin

abbrev sideB (pin : V → Option (VertexB rep)) : TwoSideStage.Side where
  C := C
  V := V
  TV := VertexB rep
  fC := inferInstance
  fV := inferInstance
  fTV := inferInstance
  len := len
  first := first
  last := last
  outgoing := @outgoingB rep
  pin := pin

theorem conditionsA (pin : V → Option (VertexA rep)) (N R : ℕ) (hR : 0 < R)
    (hroom : R + ∑ c, len c + 4*132^(2*N+1) ≤ 4260354*rep) :
    Conditions (sideA rep len first last pin) (TypedGraphs.size rep) (129/16513) N 132 R := by
  refine ⟨by norm_num,?_,?_,by norm_num,hR,?_,?_,?_⟩
  · change (Fintype.card (VertexA rep) : ℝ) ≤ (TypedGraphs.size rep : ℝ)
    simp only [← Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card,card_vertexA]
    exact le_rfl
  · intro t u h
    dsimp only [sideA]
    rw [← Nat.card_eq_fintype_card]
    simpa only [← Nat.card_eq_fintype_card, show Nat.card (VertexA rep) = TypedGraphs.size rep by
      rw [Nat.card_eq_fintype_card,card_vertexA]; rfl] using TypeWeights.joint_countA_le rep t u h
  · intro v
    exact (TypedGraphs.origin_card (@outgoingA rep) v).le.trans (degreeA_bounds v).2
  · intro x
    change R + ∑ c, len c + 4*132^(2*N+1) ≤
      Nat.card {a : TypedGraphs.Dart (@outgoingA rep) // TypedGraphs.label _ a = TypedGraphs.label _ x}
    rw [TypedGraphs.label_card,letter_frequencyA]
    exact hroom
  · obtain ⟨r,hr⟩ := TypedGraphs.conditionedA_nonempty rep N (by omega)
    refine ⟨r,?_⟩
    dsimp only [sideA,Side.samples,ConditionedMatchings.Matching.conditioned]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (Finset.mem_filter.mp hr).2

theorem conditionsB (pin : V → Option (VertexB rep)) (N R : ℕ) (hR : 0 < R)
    (hroom : R + ∑ c, len c + 4*132^(2*N+1) ≤ 4260354*rep) :
    Conditions (sideB rep len first last pin) (TypedGraphs.size rep) (129/16513) N 132 R := by
  refine ⟨by norm_num,?_,?_,by norm_num,hR,?_,?_,?_⟩
  · change (Fintype.card (VertexB rep) : ℝ) ≤ (TypedGraphs.size rep : ℝ)
    simp only [← Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card,card_vertexB]
    exact le_rfl
  · intro t u h
    dsimp only [sideB]
    rw [← Nat.card_eq_fintype_card]
    simpa only [← Nat.card_eq_fintype_card, show Nat.card (VertexB rep) = TypedGraphs.size rep by
      rw [Nat.card_eq_fintype_card,card_vertexB]; rfl] using (TypeWeights.joint_countB rep t u h).le
  · intro v
    exact (TypedGraphs.origin_card (@outgoingB rep) v).le.trans (degreeB_bounds v).2
  · intro x
    change R + ∑ c, len c + 4*132^(2*N+1) ≤
      Nat.card {a : TypedGraphs.Dart (@outgoingB rep) // TypedGraphs.label _ a = TypedGraphs.label _ x}
    rw [TypedGraphs.label_card,letter_frequencyB]
    exact hroom
  · obtain ⟨r,hr⟩ := TypedGraphs.conditionedB_nonempty rep N (by omega)
    refine ⟨r,?_⟩
    dsimp only [sideB,Side.samples,ConditionedMatchings.Matching.conditioned]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (Finset.mem_filter.mp hr).2

end TorsionFreeZeroDivisors.TypedStage

namespace TorsionFreeZeroDivisors.StageCost
open scoped BigOperators

/-- The exact vertex/table/prescription factor, before the retained turn cost. -/
def cost (n p r : ℝ) (f i e : ℕ) : ℝ := n^(f+i)*p^i/r^e

theorem cost_exp (n p r : ℝ) (hn : 0<n) (hp : 0<p) (hr : 0<r) (f i e : ℕ) :
    cost n p r f i e = Real.exp
      ((((f:ℝ)+i-e)*Real.log n) + (((i:ℝ)-e)*Real.log p) +
        e*Real.log (n*p/r)) := by
  rw [Real.log_div (ne_of_gt (mul_pos hn hp)) (ne_of_gt hr),
    Real.log_mul (ne_of_gt hn) (ne_of_gt hp)]
  have he : (((f:ℝ)+i-e)*Real.log n) + (((i:ℝ)-e)*Real.log p) +
      e*(Real.log n+Real.log p-Real.log r) =
      (f+i:ℕ)*Real.log n + (i:ℝ)*Real.log p - (e:ℝ)*Real.log r := by
    push_cast; ring
  rw [he,Real.exp_sub,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log hn,Real.exp_log hp,Real.exp_log hr]
  rfl

theorem cost_chain_exp (n p r : ℝ) (hn : 0<n) (hp : 0<p) (hr : 0<r)
    (f i e q : ℕ) (he : i+q=e) :
    cost n p r f i e = Real.exp
      (((f:ℝ)-q)*Real.log n - (q:ℝ)*Real.log p + e*Real.log (n*p/r)) := by
  rw [cost_exp n p r hn hp hr]
  congr 1
  have he' : (i:ℝ)+q=e := by exact_mod_cast he
  rw [←he']
  ring

/-- Uniform error bound, with a bounded number q of chains and e ≤ k L edges.
It keeps the exact exponent f-q, including negative and zero cases. -/
theorem uniform_bound (n p r : ℝ) (hn : 0<n) (hp : 0<p) (hp1 : p≤1)
    (hr : 0<r) (hrnp : r≤n*p) (f i e q Q : ℕ) (he : i+q=e) (hq : q≤Q)
    (k L : ℝ) (heL : (e:ℝ)≤k*L) :
    cost n p r f i e ≤ Real.exp
      (((f:ℝ)-q)*Real.log n + (Q:ℝ)*(-Real.log p) + k*L*Real.log (n*p/r)) := by
  rw [cost_chain_exp n p r hn hp hr f i e q he]
  apply Real.exp_le_exp.mpr
  have hp' : 0 ≤ -Real.log p := neg_nonneg.mpr (Real.log_nonpos hp.le hp1)
  have hr' : 0 ≤ Real.log (n*p/r) := Real.log_nonneg ((le_div_iff₀ hr).mpr (by simpa using hrnp))
  have hq' := mul_le_mul_of_nonneg_right (show (q:ℝ)≤Q by exact_mod_cast hq) hp'
  have he' := mul_le_mul_of_nonneg_right heL hr'
  linarith

theorem internal_add_chains {C : Type*} [Fintype C] (len : C → ℕ) (hpos : ∀c,0<len c) :
    (∑c, (len c-1))+Fintype.card C=∑c,len c := by
  classical
  have h : (∑c : C, ((len c-1)+1)) = ∑c : C,len c := by
    apply Finset.sum_congr rfl
    intro c _
    exact Nat.sub_add_cancel (hpos c)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using h

end TorsionFreeZeroDivisors.StageCost

namespace TorsionFreeZeroDivisors.StageDenominator

section
open scoped Topology
open Filter GirthAsymptotics TypedGraphs

theorem carrier_eq (rep : ℕ) : (carrier rep : ℝ) = (size rep : ℝ)*(129/16513) := by
  simp only [carrier,size,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

end

open scoped BigOperators Topology
open Filter GirthAsymptotics TypedGraphs TwoSideStage

/-- Each side has the SAME empirical carrier denominator, not the sum of the
sizes of the two disjoint graphs. This bound is uniform in every stage. -/
theorem room (K rep e : ℕ) (hr : K*L (size rep)+exclusion (size rep) ≤ carrier rep)
    (he : e ≤ K*L (size rep)) :
    denominator K rep+e+4*132^(2*(3*L (size rep))+1) ≤ 4260354*rep := by
  have hh : 2*(3*L (size rep))=6*L (size rep) := by omega
  rw [hh]
  change denominator K rep+e+exclusion (size rep) ≤ carrier rep
  dsimp only [denominator]
  omega

variable {C V : Type} [Fintype C] [Fintype V]

theorem conditionsA (K rep : ℕ) (hr : K*L (size rep)+exclusion (size rep)<carrier rep)
    (len : C → ℕ) (first last : C → V) (pin : V → Option (Types.VertexA rep))
    (he : ∑c,len c ≤ K*L (size rep)) :
    Conditions (TypedStage.sideA rep len first last pin) (size rep) (129/16513)
      (3*L (size rep)) 132 (denominator K rep) :=
  TypedStage.conditionsA rep len first last pin _ _ (Nat.sub_pos_of_lt hr)
    (room K rep _ hr.le he)

theorem conditionsB (K rep : ℕ) (hr : K*L (size rep)+exclusion (size rep)<carrier rep)
    (len : C → ℕ) (first last : C → V) (pin : V → Option (Types.VertexB rep))
    (he : ∑c,len c ≤ K*L (size rep)) :
    Conditions (TypedStage.sideB rep len first last pin) (size rep) (129/16513)
      (3*L (size rep)) 132 (denominator K rep) :=
  TypedStage.conditionsB rep len first last pin _ _ (Nat.sub_pos_of_lt hr)
    (room K rep _ hr.le he)

/-- The edge/table cost is an exponential of f-q log n plus a uniform o(L),
for two sides jointly. The signed value f-q is NOT replaced by its positive part. -/
theorem joint_cost_bound (A B : Side) (K Q rep : ℕ) (hn : 0<size rep)
    (hr : 0<denominator K rep) (ha : ∀c,0<A.len c) (hb : ∀c,0<B.len c)
    (hQ : Fintype.card A.C+Fintype.card B.C ≤ Q)
    (hE : A.edges+B.edges ≤ K*L (size rep)) :
    A.cost (size rep) (129/16513) (denominator K rep) *
      B.cost (size rep) (129/16513) (denominator K rep) ≤
      Real.exp ((((A.freeMarks+B.freeMarks:ℕ):ℝ)-
        (Fintype.card A.C+Fintype.card B.C:ℕ))*Real.log (size rep)+error K Q rep) := by
  have hAI := StageCost.internal_add_chains A.len ha
  have hBI := StageCost.internal_add_chains B.len hb
  have he : A.internal+B.internal+(Fintype.card A.C+Fintype.card B.C)=A.edges+B.edges := by
    dsimp only [Side.internal,Side.edges] at *
    omega
  have hrnp : (denominator K rep:ℝ) ≤ (size rep:ℝ)*(129/16513) := by
    rw [←carrier_eq]
    exact Nat.cast_le.mpr (Nat.sub_le ..)
  have h := StageCost.uniform_bound (size rep) (129/16513) (denominator K rep)
    (by exact_mod_cast hn) (by norm_num) (by norm_num) (by exact_mod_cast hr) hrnp
    (A.freeMarks+B.freeMarks) (A.internal+B.internal) (A.edges+B.edges)
    (Fintype.card A.C+Fintype.card B.C) Q he hQ K (L (size rep)) (by exact_mod_cast hE)
  have hc : A.cost (size rep) (129/16513) (denominator K rep)*
      B.cost (size rep) (129/16513) (denominator K rep) =
      StageCost.cost (size rep) (129/16513) (denominator K rep)
        (A.freeMarks+B.freeMarks) (A.internal+B.internal) (A.edges+B.edges) := by
    rw [cost_product]
    unfold StageCost.cost
    have hex : A.freeMarks+A.internal+B.freeMarks+B.internal =
        (A.freeMarks+B.freeMarks)+(A.internal+B.internal) := by omega
    rw [hex]
  rw [hc]
  simpa only [error,penalty,add_assoc] using h

end TorsionFreeZeroDivisors.StageDenominator

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageEntropy

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ)
    (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)
    (d : Underlying s len → ℤ)

/-- The literal label/bin exponent, in the stage bound. -/
def labelCost (j : ℕ) : ℝ :=
  (∑ c : StageLabels.activeComponents
    (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
      ActualStageLabels.cost s hs len m cmp err d c.val) -
    ∑ i ∈ activeBlocks s len m j, (d i : ℝ)

theorem labelCost_eq (M : ℕ) (j : Fin M) :
    labelCost s hs len m cmp err d j =
      LinkComponents.stageCost (multiplicity s len m) (ActualStageLabels.P s hs len m cmp err)
        M (fun i => (d i : ℝ)) (1/600) s j := by
  unfold labelCost
  change (∑ c : StageLabels.activeComponents
    (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk
    (Finset.univ.filter (fun i => j.val < multiplicity s len m i)),
      ActualStageLabels.cost s hs len m cmp err d c.val) - _ = _
  rw [ActualStageLabels.cost_sum]
  simp only [activeBlocks,Finset.sum_filter,LinkComponents.stageCost,
    ActualStageLabels.cost,RepeatedBlocks.multiplicity]
  rw [sub_eq_add_neg]
  rw [add_comm]
  congr! 3

/-- The source uniform block-propagation and chain-tail error, before taking
limits. All blocks and both sides are counted only once. -/
def looseCost : ℝ :=
  (2*(err : ℝ)*Fintype.card (Underlying s len)+(s+1)*Fintype.card C)*
    Real.log (Fintype.card Letter)

/-- Literal component costs dispatched through proven unmatched-incidence
and layer-cake estimates. The power hypothesis is the (separate) actual
immersed-path vertex/edge inequality, not a first-moment assumption. -/
theorem sum_exponents (M : ℕ) (hm : ∀ c, m c ≤ M) (a logn : ℝ)
    (power error : Fin M → ℝ) (ha : 0≤a) (hn : 0≤logn)
    (hlow : ∀ i, (1/600:ℝ)*s/2 ≤ d i) (hhigh : ∀ i, (d i : ℝ) ≤ a*s)
    (hpower : ∑ j, power j ≤ 0) :
    (Finset.univ.sum (fun j : Fin M => power j*logn + labelCost s hs len m cmp err d j.val + error j)) ≤
      a*s*Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched -
        (1/1200:ℝ)*s*(∑ i : Underlying s len, (multiplicity s len m i : ℝ)) +
          ∑ j : Fin M, error j := by
  simp_rw [labelCost_eq]
  convert LinkComponents.sum_stageBound (multiplicity s len m)
    (ActualStageLabels.P s hs len m cmp err) M (fun i => hm i.1)
    (fun i => (d i : ℝ)) (1/600) s a logn power error
    (by norm_num) hs.le ha hn hlow hhigh hpower using 1
  norm_num
  left
  congr! 3

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate TwoSideFullStage
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)
variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.StageEntropy

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*} (D : OccurrenceMatching.Data (Ω := Ω) (B := B) (E := E))

def transportUnmatched (r : B' ≃ B) : (D.transport r).matching.Unmatched ≃ D.matching.Unmatched where
  toFun o := ⟨r o.val,by
    rw [← D.transport_partner r o.val,o.property]⟩
  invFun o := ⟨r.symm o.val,by
    apply r.injective
    rw [D.transport_partner,r.apply_symm_apply,o.property]⟩
  left_inv o := Subtype.ext (r.symm_apply_apply o.val)
  right_inv o := Subtype.ext (r.apply_symm_apply o.val)

variable [Fintype B]
theorem card_unmatched : Fintype.card D.matching.Unmatched = D.unmatchedBlocks.card := by
  change Fintype.card {o : B // D.matching.partner o = o} = _
  rw [Fintype.card_subtype]
  rfl
end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.StageMass

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ)
  (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def totalLength : ℝ := ∑ t : Traversal m, (traversalLength len m t : ℝ)
def uncovered : ℕ := (cmp.matchingData s hs (traversalLength len m) err).unpairedPositions.card

theorem unmatched_card : Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched =
    (cmp.matchingData s hs (traversalLength len m) err).unmatchedBlocks.card := by
  rw [← OccurrenceMatching.Data.card_unmatched]
  convert Fintype.card_congr
    ((cmp.matchingData s hs (traversalLength len m) err).transportUnmatched (occurrenceEquiv s len m).symm) using 1 <;> congr! 3

variable [Fintype E]
/-- The occurrence involution used by the entropy components has exactly the
unmatched mass of the literal half-integer comparisons. -/
theorem unmatched_bound (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err) :
    s*Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched ≤
      uncovered s hs len m cmp err + 22*s*Fintype.card E + totalLength len m/s := by
  rw [unmatched_card]
  exact cmp.unmatched_bound s hs (traversalLength len m) err ν hsmall herr

omit [Fintype E] in
/-- Repeated traversal length is counted with its actual multiplicity. -/
theorem totalLength_eq : totalLength len m = ∑ c, (m c:ℝ)*len c := by
  simp only [totalLength,Fintype.sum_sigma,traversalLength,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

omit [Fintype E] in
theorem fullMass_eq : (∑ i : Underlying s len, (multiplicity s len m i:ℝ)) =
    ∑ c, (blockCount s (len c):ℝ)*m c := by
  simp only [Underlying,Block,Fintype.sum_sigma,RepeatedBlocks.multiplicity,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

omit [Fintype E] in
include hs in
/-- The only mass lost from full blocks is at the ends of actual chain
traversals. In particular repeated paths do not reduce this loss count. -/
theorem fullMass_lower : totalLength len m ≤
    s*(∑ i : Underlying s len, (multiplicity s len m i:ℝ)) + s*(∑ c,(m c:ℝ)) := by
  rw [totalLength_eq,fullMass_eq,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have h := mul_le_mul_of_nonneg_left (count_bound s hs (len c)).2.le (Nat.cast_nonneg (m c): (0:ℝ) ≤ m c)
  nlinarith

omit [Fintype E] in
include hs in
theorem fullMass_lower_bounded (M Q : ℕ) (hm : ∀ c,m c≤M) (hQ : Fintype.card C≤Q) :
    totalLength len m ≤ s*(∑ i : Underlying s len, (multiplicity s len m i:ℝ)) + s*(M:ℝ)*Q := by
  have hm' : (∑ c,(m c:ℝ)) ≤ (M:ℝ)*Q := by
    calc
      _ ≤ ∑ _c : C,(M:ℝ) := Finset.sum_le_sum (fun c _ => by exact_mod_cast hm c)
      _ = (M:ℝ)*Fintype.card C := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hQ) (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left hm' hs.le
  have hmass := fullMass_lower s hs len m
  nlinarith

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] [Fintype E]
  (s : ℝ) (hs : 0<s) (len m : C → ℕ)
  (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def residual (M Q : ℕ) (denError : ℝ) : ℝ :=
  256*(22*s*Fintype.card E+totalLength len m/s) +
    (1/1200:ℝ)*s*M*Q + M*(StageEntropy.looseCost s len err+denError)

/-- All explicit finite stage losses, before the common-scale limit. -/
theorem exponent_sum_bound (M Q : ℕ) (hm : ∀ c,m c≤M) (hQ : Fintype.card C≤Q)
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (d : Underlying s len → ℤ) (hlow : ∀ i,(1/600:ℝ)*s/2≤d i)
    (hhigh : ∀ i,(d i:ℝ)≤256*s)
    (logn denError : ℝ) (hn : 0≤logn) (power : Fin M → ℝ)
    (hpower : ∑ j,power j≤0) :
    (Finset.univ.sum (fun j : Fin M => power j*logn+
      StageEntropy.labelCost s hs len m cmp err d j.val+
      (StageEntropy.looseCost s len err+denError))) ≤
        -(1/1200:ℝ)*totalLength len m + 256*uncovered s hs len m cmp err+
          residual (E := E) s len m err M Q denError := by
  have h := StageEntropy.sum_exponents s hs len m cmp err d M hm 256 logn power
    (fun _ => StageEntropy.looseCost s len err+denError) (by norm_num) hn hlow hhigh hpower
  have hu := unmatched_bound s hs len m cmp err ν hsmall herr
  have hf := fullMass_lower_bounded s hs len m M Q hm hQ
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  unfold residual
  linarith

/-- Concrete finite selection input: only an actual uncovered-length bound
and the independently controlled remainder are needed. -/
theorem decay (M Q : ℕ) (hm : ∀ c,m c≤M) (hQ : Fintype.card C≤Q)
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (d : Underlying s len → ℤ) (hlow : ∀ i,(1/600:ℝ)*s/2≤d i)
    (hhigh : ∀ i,(d i:ℝ)≤256*s)
    (logn denError : ℝ) (hn : 0≤logn) (power : Fin M → ℝ)
    (hpower : ∑ j,power j≤0)
    (hb : (uncovered s hs len m cmp err:ℝ) ≤ StageFusion.epsilon (1/600) 256*totalLength len m)
    (he : residual (E := E) s len m err M Q denError ≤ totalLength len m/4800) :
    (Finset.univ.sum (fun j : Fin M => power j*logn+
      StageEntropy.labelCost s hs len m cmp err d j.val+
      (StageEntropy.looseCost s len err+denError))) ≤ -totalLength len m/2400 := by
  have h := exponent_sum_bound s hs len m cmp err M Q hm hQ ν hsmall herr
    d hlow hhigh logn denError hn power hpower
  have hH : 0≤totalLength len m := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have ha := StageFusion.absorb_errors (δ := 1/600) (a := 256) (by norm_num) (by norm_num) hH hb
    (by linarith : residual (E := E) s len m err M Q denError ≤ (1/600:ℝ)*totalLength len m/8)
  linarith
end TorsionFreeZeroDivisors.StageMass

namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

def values (s : ℝ) : Finset ℤ := Finset.Icc 0 ⌊256*s⌋
def profiles {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ) : Finset (Underlying s len → ℤ) :=
  Fintype.piFinset (fun _ => values s)

theorem card_values (s : ℝ) (hs : 0 ≤ s) : ((values s).card:ℝ) ≤ 256*s+1 := by
  have hf : (0:ℤ)≤⌊256*s⌋ := Int.floor_nonneg.mpr (by positivity)
  have hcast : ((⌊256*s⌋+1).toNat:ℝ) = (⌊256*s⌋:ℝ)+1 := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega),Int.cast_add,Int.cast_one]
  simp only [values,Int.card_Icc,sub_zero]
  rw [hcast]
  linarith [Int.floor_le (256*s)]

variable {C : Type*} [Fintype C]
theorem card_profiles (s : ℝ) (len : C → ℕ) (hs : 0 ≤ s) :
    ((profiles s len).card:ℝ) ≤ Real.exp (Fintype.card (Underlying s len)*Real.log (256*s+1)) := by
  have hp : 0<256*s+1 := by positivity
  rw [profiles,Fintype.card_piFinset,Finset.prod_const,Finset.card_univ,Nat.cast_pow]
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (card_values s hs) _).trans_eq
  rw [Real.exp_nat_mul,Real.exp_log hp]

/-- The number of all integer bin assignments is exponentially bounded by the
actual full-block mass. There is no independence assumption between bins. -/
theorem cardinal_bound (s : ℝ) (hs : 0<s) (len : C → ℕ) :
    ((profiles s len).card:ℝ) ≤ Real.exp
      (((∑ c,(len c:ℝ))/s)*Real.log (256*s+1)) := by
  apply (card_profiles s len hs.le).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · exact (le_div_iff₀ hs).mpr (by simpa [mul_comm] using Comparisons.block_mass s hs len)
  · exact Real.log_nonneg (by linarith)
end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.GridAsymptotics
open Filter Topology
open scoped Classical

theorem R_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : 0 < R d L := by
  apply Nat.floor_pos.mpr
  apply Real.le_sqrt_of_sq_le
  norm_num
  exact_mod_cast N_pos d hL

theorem R_le_N (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : R d L ≤ N d L := by
  apply Nat.floor_le_of_le
  apply Real.sqrt_le_iff.mpr
  have hn : (1 : ℝ) ≤ N d L := by exact_mod_cast N_pos d hL
  constructor <;> nlinarith

theorem denominator_le_sqrt (d : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ((N d L : ℝ)^d * R d L) ≤ Real.sqrt L := by
  have hn : (N d L : ℝ) ≤ L ^ exponent d := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
  have hr : (R d L : ℝ) ≤ N d L := by exact_mod_cast R_le_N d hL
  calc
    _ ≤ (N d L : ℝ)^d * N d L := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (N d L : ℝ)^(d+1) := (pow_succ _ _).symm
    _ ≤ (L ^ exponent d)^(d+1) := pow_le_pow_left₀ (by positivity) hn _
    _ = L ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 1
      push_cast
      unfold exponent
      field_simp
    _ = Real.sqrt L := (Real.sqrt_eq_rpow _).symm

theorem scale_bounds (d : ℕ) {L : ℝ} (hL : 1 ≤ L) {u : ℕ}
    (hu : 1 ≤ u) (hub : u ≤ (N d L)^d) :
    Real.sqrt L ≤ scale d L u ∧ scale d L u / L ≤ 1/(R d L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hRp : (0 : ℝ) < R d L := by exact_mod_cast R_pos d hL
  have hup : (0 : ℝ) < u := by exact_mod_cast hu
  have huR : ((u : ℝ)*R d L) ≤ Real.sqrt L := by
    have hubr : (u : ℝ) ≤ (N d L : ℝ)^d := by exact_mod_cast hub
    apply le_trans (mul_le_mul_of_nonneg_right hubr hRp.le)
    simpa using denominator_le_sqrt d hL
  constructor
  · unfold scale
    apply (le_div_iff₀ (mul_pos hup hRp)).mpr
    have hs := Real.sq_sqrt hLp.le
    have ht := mul_le_mul_of_nonneg_left huR (Real.sqrt_nonneg L)
    nlinarith
  · have hs : scale d L u ≤ L / (R d L : ℝ) := by
      unfold scale
      apply div_le_div_of_nonneg_left hLp.le hRp
      have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
      nlinarith
    apply (div_le_iff₀ hLp).mpr
    simpa [div_eq_mul_inv,mul_comm] using hs

theorem chosen_spec (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    Compatible d L offset (chosenU d L offset) := by
  unfold chosenU
  rw [dif_pos hL]
  exact Nat.find_spec _

theorem chosen_min (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) {v : ℕ}
    (hv : Compatible d L offset v) : chosenU d L offset ≤ v := by
  unfold chosenU
  rw [dif_pos hL]
  exact Nat.find_min' _ hv

theorem chosen_bound (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    chosenU d L offset ≤ (N d L)^d := by
  obtain ⟨u,hu,hub,z,hz⟩ := BlockGrid.simultaneous (N_pos d hL) (fun i => (offset i : ℝ)/L)
  exact (chosen_min d hL offset ⟨hu,z,hz⟩).trans hub

theorem chosen_alignment (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    ∃ ν : Fin d → ℤ, ∀ i,
      |(offset i : ℝ)/chosenScale d L offset-(ν i : ℝ)| < (R d L : ℝ)/(N d L) := by
  obtain ⟨hu,z,hz⟩ := chosen_spec d hL offset
  refine ⟨fun i => (R d L : ℤ)*z i,fun i => ?_⟩
  have hLp : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
  have hR : (0 : ℝ) < R d L := by exact_mod_cast R_pos d hL
  have hh := mul_lt_mul_of_pos_left (hz i) hR
  have he : (offset i : ℝ)/chosenScale d L offset-((R d L : ℤ)*z i : ℤ) =
      (R d L : ℝ)*((chosenU d L offset : ℝ)*((offset i : ℝ)/L)-(z i : ℝ)) := by
    simp only [chosenScale,scale,Int.cast_mul,Int.cast_natCast]
    field_simp
  rw [he,abs_mul,abs_of_pos hR]
  simpa [div_eq_mul_inv,mul_assoc] using hh

theorem chosenScale_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    0 < chosenScale d L offset := by
  exact lt_of_lt_of_le (Real.sqrt_pos.mpr (by linarith))
    (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1

theorem letterError_bounds (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4 ≤ letterError d L offset ∧
    (letterError d L offset : ℝ) ≤
      2*((R d L : ℝ)/(N d L))*chosenScale d L offset+5 := by
  constructor
  · exact Nat.le_ceil _
  · have hs := chosenScale_pos d hL offset
    have hh := Nat.ceil_lt_add_one (show 0 ≤
        2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4 by
        positivity)
    dsimp only [letterError]
    linarith

theorem uniform_alignment (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    ∃ ν : Fin d → ℤ, ∀ i,
      2*|(offset i : ℝ)-(ν i : ℝ)*chosenScale d L offset|+4 ≤ letterError d L offset := by
  obtain ⟨ν,hν⟩ := chosen_alignment d hL offset
  refine ⟨ν,fun i => ?_⟩
  have hs := chosenScale_pos d hL offset
  have hh := (mul_lt_mul_of_pos_right (hν i) hs).le
  have he : |(offset i : ℝ)/chosenScale d L offset-(ν i : ℝ)| *chosenScale d L offset =
      |(offset i : ℝ)-(ν i : ℝ)*chosenScale d L offset| := by
    rw [← abs_of_pos hs,← abs_mul]
    congr 1
    rw [abs_of_pos hs]
    field_simp
  rw [he] at hh
  have hr := (letterError_bounds d hL offset).1
  nlinarith

end TorsionFreeZeroDivisors.GridAsymptotics

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

theorem rate_nonneg (d : ℕ) {L : ℝ} (hL : 0≤L) : 0≤rate d L := by
  unfold rate
  positivity

/-- A single offset-independent rate controls every scalar rounding loss. -/
theorem bounds (d : ℕ) {L : ℝ} (hL : 1≤L) (offset : Fin d → ℤ) :
    chosenScale d L offset/L ≤ rate d L ∧
    1/chosenScale d L offset ≤ rate d L ∧
    (letterError d L offset:ℝ)/chosenScale d L offset ≤ 5*rate d L ∧
    1/L ≤ rate d L := by
  have hL0 : 0<L := by linarith
  have hs := chosenScale_pos d hL offset
  have hroot := Real.sqrt_pos.mpr hL0
  have hb := scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)
  change Real.sqrt L ≤ chosenScale d L offset ∧
    chosenScale d L offset/L ≤ 1/(R d L:ℝ) at hb
  have hi : 1/chosenScale d L offset ≤ 1/Real.sqrt L :=
    one_div_le_one_div_of_le hroot hb.1
  have he : (letterError d L offset:ℝ)/chosenScale d L offset ≤
      2*((R d L:ℝ)/(N d L))+5/chosenScale d L offset := by
    apply (div_le_iff₀ hs).mpr
    have hh := (letterError_bounds d hL offset).2
    have hh' : (2*((R d L:ℝ)/(N d L))+5/chosenScale d L offset)*chosenScale d L offset =
        2*((R d L:ℝ)/(N d L))*chosenScale d L offset+5 := by field_simp
    rwa [hh']
  have hr : 0 ≤ 1/(R d L:ℝ) := by positivity
  have hn : 0 ≤ (R d L:ℝ)/(N d L) := by positivity
  have hlo : 0 ≤ 1/L := by positivity
  have hso : 0 ≤ 1/Real.sqrt L := by positivity
  unfold rate
  simp only [div_eq_mul_inv,one_mul] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.StageUniform
open scoped Classical BigOperators Topology
open BlockAlignment ComparedBlocks RepeatedBlocks GridAsymptotics Filter

theorem alphabetLog_nonneg : 0 ≤ alphabetLog := by
  apply Real.log_nonneg
  norm_num [WordEstimate.Letter]

/-- Uniform scalar estimate. Its inputs are just the explicit common-grid
loss bounds, not an entropy or probability estimate. -/
theorem scalar_bound (D K M Q : ℕ) (L s H blocks err rate den : ℝ)
    (hL : 0 < L) (hs : 0 < s) (_hH : 0 ≤ H) (hb : 0 ≤ blocks)
    (hr : 0 ≤ rate) (hscale : s/L≤ rate) (hinv : 1/s≤ rate)
    (hone : 1/L≤ rate) (he : err/s≤5*rate)
    (hsize : H≤K*L) (hblocks : s*blocks≤K*L) :
    (256*(22*s*D+H/s)+(1/1200:ℝ)*s*M*Q+
      M*((2*err*blocks+(s+1)*Q)*alphabetLog+den))/L ≤
        coefficient D K M Q*rate+M*den/L := by
  have hsl := (div_le_iff₀ hL).mp hscale
  have hon := (div_le_iff₀ hL).mp hone
  have he' := (div_le_iff₀ hs).mp he
  have hHl : H/s ≤ (K:ℝ)*L*rate := by
    calc
      _ ≤ ((K:ℝ)*L)/s := div_le_div_of_nonneg_right hsize hs.le
      _ = ((K:ℝ)*L)*(1/s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  have heb := mul_le_mul_of_nonneg_right he' hb
  have hbc := mul_le_mul_of_nonneg_left hblocks (show 0 ≤ 10*rate by positivity)
  have htail : (s+1)*(Q:ℝ) ≤ 2*rate*L*Q :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg Q)
  have hloss : 2*err*blocks+(s+1)*Q ≤ (10*K+2*Q)*rate*L := by nlinarith
  have hlog := mul_le_mul_of_nonneg_right hloss alphabetLog_nonneg
  have hst := mul_le_mul_of_nonneg_right hsl (show 0 ≤ 22*(D:ℝ) by positivity)
  have hsq := mul_le_mul_of_nonneg_right hsl (show 0 ≤ (1/1200:ℝ)*M*Q by positivity)
  have hM := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
  apply (div_le_iff₀ hL).mpr
  have hcancel : (coefficient D K M Q*rate+M*den/L)*L =
      coefficient D K M Q*rate*L+M*den := by field_simp
  rw [hcancel]
  unfold coefficient
  nlinarith

variable {C E : Type*} [Fintype C] [Fintype E]

/-- Specialization to the literal stage remainder: the ONLY scale-dependent
upper bound is `rate`, which does not mention offsets or labelled words. -/
theorem residual_bound (K M Q : ℕ) (L : ℝ) (hL : 1≤L)
    (offset : Fin (Fintype.card E) → ℤ) (len m : C → ℕ) (hQ : Fintype.card C≤Q)
    (hH : StageMass.totalLength len m ≤ K*L) (hpositive : ∀ c,1≤ m c) (den : ℝ) :
    StageMass.residual (E := E) (chosenScale (Fintype.card E) L offset) len m
      (letterError (Fintype.card E) L offset) M Q den/L ≤
        coefficient (Fintype.card E) K M Q*GridUniform.rate (Fintype.card E) L+M*den/L := by
  let s := chosenScale (Fintype.card E) L offset
  let err := letterError (Fintype.card E) L offset
  have hs : 0 < s := chosenScale_pos _ hL offset
  have hcard : s*Fintype.card (Underlying s len) ≤ (K:ℝ)*L := by
    apply (Comparisons.block_mass s hs len).trans
    apply le_trans ?_ hH
    rw [StageMass.totalLength_eq]
    apply Finset.sum_le_sum
    intro c _
    have hp : (1:ℝ)≤ m c := by exact_mod_cast hpositive c
    have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (len c): (0:ℝ) ≤ len c)
    simpa only [one_mul] using hm
  have hr := GridUniform.bounds (Fintype.card E) hL offset
  have h := scalar_bound (Fintype.card E) K M Q L s (StageMass.totalLength len m)
    (Fintype.card (Underlying s len)) err (GridUniform.rate (Fintype.card E) L) den
    (by linarith) hs (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    (Nat.cast_nonneg _) (GridUniform.rate_nonneg _ (by linarith))
    hr.1 hr.2.1 hr.2.2.2 hr.2.2.1 hH hcard
  apply le_trans ?_ h
  apply div_le_div_of_nonneg_right _ (by linarith)
  unfold StageMass.residual StageEntropy.looseCost alphabetLog
  have htail := mul_le_mul_of_nonneg_left (show (Fintype.card C:ℝ) ≤ Q by exact_mod_cast hQ)
    (show 0 ≤  s+1 by linarith)
  have hlog := mul_le_mul_of_nonneg_right htail alphabetLog_nonneg
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
  dsimp only [alphabetLog] at hh
  linarith

open GirthAsymptotics TypedGraphs

end TorsionFreeZeroDivisors.StageUniform
namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

theorem scale_le (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    chosenScale d L offset ≤ L := by
  have h := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).2
  change chosenScale d L offset/L ≤ 1/(R d L:ℝ) at h
  have hR : (1:ℝ) ≤ R d L := by exact_mod_cast R_pos d hL
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hR
  norm_num only [div_one] at hi
  have hh := (div_le_iff₀ (show 0<L by linarith)).mp (h.trans hi)
  simpa only [one_mul] using hh

/-- A single common-grid bound for the logarithm of the number of all bin
profiles, without fixing any comparison offsets. -/
theorem bin_bound (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    Real.log (256*chosenScale d L offset+1)/chosenScale d L offset ≤ binRate L := by
  let s := chosenScale d L offset
  have hs : 0<s := chosenScale_pos d hL offset
  have hsl : s ≤ L := scale_le d hL offset
  have hlo := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1
  change Real.sqrt L ≤ s at hlo
  have hL0 : 0<L := by linarith
  have hlog := Real.log_le_log (show 0<256*s+1 by positivity)
    (show 256*s+1 ≤ 257*L by linarith)
  rw [Real.log_mul (by norm_num : (257:ℝ)≠0) hL0.ne'] at hlog
  calc
    _ ≤ (Real.log 257+Real.log L)/s := div_le_div_of_nonneg_right hlog hs.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity [Real.log_nonneg hL])
      (Real.sqrt_pos.mpr hL0) hlo

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] [Fintype E]

omit [Fintype C] in
theorem height_bounds (s : ℝ) (hs : 0 ≤ s) (len : C → ℕ) (i : Underlying s len) :
    s-1 ≤ (height s len i:ℝ) ∧ (height s len i:ℝ) ≤ s+1 := by
  have hl := card_lower ((i.2.val:ℝ)*s) (((i.2.val:ℝ)+1)*s)
  have hu := card_upper (lo := (i.2.val:ℝ)*s) (hi := ((i.2.val:ℝ)+1)*s) (by nlinarith)
  simp only [height,block,Int.cast_natCast]
  constructor <;> linarith

end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

include e in
omit [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T] in
theorem immersed : Function.Injective (fun d => (Γ.origin d,plabel d)) := by
  intro d f h
  apply e.port.injective
  apply Subtype.ext
  apply Prod.ext
  · change origin outgoing (e.port d) = origin outgoing (e.port f)
    rw [e.origin_eq,e.origin_eq]
    exact congrArg e.vertex (congrArg Prod.fst h)
  · change label outgoing (e.port d) = label outgoing (e.port f)
    rw [e.label_eq,e.label_eq]
    exact congrArg Prod.snd h

def vertexMap : VertexMap (StageRealization.allowed Γ plabel outgoing pin) :=
  ⟨e.vertex,e.vertex.injective,by
    intro v
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,e.pin_eq v⟩
    intro d hd
    have hp := (e.port d).property
    change label outgoing (e.port d) ∈ outgoing (origin outgoing (e.port d)) at hp
    simpa only [e.label_eq,e.origin_eq,hd] using hp⟩

omit [Fintype PV] [Fintype T] in
theorem dartMap_eq (d : PD) :
    dartMap Γ plabel outgoing _ (StageRealization.allowed_ports Γ plabel outgoing pin)
      (vertexMap e) d = e.port d := by
  apply Subtype.ext
  apply Prod.ext
  · exact (e.origin_eq d).symm
  · exact (e.label_eq d).symm

include e in
omit [Fintype T] in
/-- A literal embedding contributes at least one to the exact realization
count. The event direction is explicit rather than postulated. -/
theorem realizations_pos : 0 < StageRealization.realizations Γ plabel outgoing pin bar r := by
  apply Finset.card_pos.mpr
  refine ⟨vertexMap e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  intro d
  rw [dartMap_eq,dartMap_eq]
  exact e.reverse_eq d

variable {PV' PD' : Type*} [Fintype PV'] [Fintype PD']

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
variable {W : Type*}

/-- Every actual globally compatible embedding is contained in the event
counted by the two-side first moment. -/
theorem count_pos (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (r : A.Match × B.Match) (w : W) (hw : w∈X)
    (eA : RealizationTransport.Embedding (ChainSubdivision.graph A.len A.first A.last)
      (ChainRealization.label A.len (StageExpectation.readWord A.len (WA w))) A.outgoing
      (ChainRealization.pin A.len A.pin) Types.inverse r.1)
    (eB : RealizationTransport.Embedding (ChainSubdivision.graph B.len B.first B.last)
      (ChainRealization.label B.len (StageExpectation.readWord B.len (WB w))) B.outgoing
      (ChainRealization.pin B.len B.pin) Types.inverse r.2) :
    0<count A B X WA WB r := by
  have hm : w∈immersedLabels A B X WA WB :=
    Finset.mem_filter.mpr ⟨hw,RealizationTransport.immersed eA,RealizationTransport.immersed eB⟩
  have hp : 0<A.realizations (WA w) r.1*B.realizations (WB w) r.2 :=
    Nat.mul_pos (RealizationTransport.realizations_pos eA) (RealizationTransport.realizations_pos eB)
  apply hp.trans_le
  unfold count
  exact Finset.single_le_sum (f := fun w => A.realizations (WA w) r.1 * B.realizations (WB w) r.2)
    (fun _ _ => Nat.zero_le _) hm

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T QV QD : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]
    [Fintype QV] [Fintype QD]
variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

/-- Restriction needs only injectivity, not a bijection onto the whole image.
In particular, inactive marked vertices are never carried into a stage. -/
def restrict (Q : PortGraph QV QD) (fv : QV ↪ PV) (fd : QD ↪ PD)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d)) (pin' : QV → Option TV)
    (hp : ∀ v y,pin' v=some y → pin (fv v)=some y) :
    Embedding Q (plabel ∘ fd) outgoing pin' bar r where
  vertex := fv.trans e.vertex
  port := fd.trans e.port
  origin_eq d := by simpa only [Function.Embedding.trans_apply,ho] using e.origin_eq (fd d)
  label_eq d := e.label_eq (fd d)
  reverse_eq d := by simpa only [Function.Embedding.trans_apply,hr] using e.reverse_eq (fd d)
  pin_eq v y hy := e.pin_eq (fv v) y (hp v y hy)

/-- Change the displayed port labeling by a literal pointwise equality. -/
def congrLabel (label' : PD → T) (hl : ∀ d,label' d=plabel d) :
    Embedding Γ label' outgoing pin bar r where
  vertex := e.vertex
  port := e.port
  origin_eq := e.origin_eq
  label_eq d := (e.label_eq d).trans (hl d).symm
  reverse_eq := e.reverse_eq
  pin_eq := e.pin_eq

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.ActualStageRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "len" => ChainStageEmbedding.length Γ mark h2 paths j
local notation "Q" => ChainStageEmbedding.graph Γ mark h2 paths j
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)

/-- The actual signed labels, at every position of every active chain. -/
def word (label : D → Types.Letter) : ComparedBlocks.Position len → WordEstimate.Letter :=
  fun x => Types.signedLetter.symm (label (F^[x.2.val.toNat] x.1.val.val.val))

lemma index_mem (c : ChainActiveStages.ActiveChain Γ mark h2 paths j) (i : Fin (len c)) :
    (i.val:ℤ)∈BlockAlignment.positions 0 (len c) := by
  rw [AffineIntervals.nat_positions]
  simp only [Finset.mem_Ico]
  constructor
  · omega
  · exact_mod_cast i.isLt

lemma label_eq (label : D → Types.Letter) (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (d : ChainSubdivision.Dart len) :
    ChainRealization.label len (StageExpectation.readWord len (word Γ mark h2 paths j label)) d =
      label (ChainStageEmbedding.dartMap Γ mark h2 paths j d) := by
  rcases d with ⟨⟨c,i⟩,b⟩
  have hi := index_mem Γ mark h2 paths j c i
  cases b <;>
    simp only [ChainRealization.label,Bool.false_eq_true,ite_false,ite_true,StageExpectation.readWord,
      dif_pos hi,word,Int.toNat_natCast,Types.signedLetter.apply_symm_apply,
      ChainStageEmbedding.dartMap,Function.comp_apply,SubdivisionRestriction.dart,ChainIsomorphism.dartMap,hl]

variable [Fintype V] {TV : Type} [Fintype TV]
    {outgoing : TV → Finset Types.Letter} {pin : V → Option TV}
    {r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse}

end TorsionFreeZeroDivisors.ActualStageRealization

namespace TorsionFreeZeroDivisors.ActualStageFeasibility
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

lemma signed_inverse (t : Types.Letter) :
    Types.signedLetter.symm (Types.inverse t)=inverse (Types.signedLetter.symm t) := by
  simp [Types.inverse,inverse]

lemma signed_choice (b : Bool) (t : Types.Letter) :
    Types.signedLetter.symm (if b then Types.inverse t else t)=
      if b then inverse (Types.signedLetter.symm t) else Types.signedLetter.symm t := by
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,signed_inverse]

lemma weight_pos {t u : Letter} (h : u≠inverse t) : 0 < weight t u := by
  unfold weight baseWeight p
  simp only [if_neg h]
  split_ifs <;> norm_num

variable {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)

omit [Fintype C] in
lemma block_weight_pos (w : C → ℤ → Letter) (hw : ActualStageLabels.Immersed s len w)
    (i : Underlying s len) : 0 < wordWeight (height s len i) (RepeatedBlocks.word s len w i) := by
  rw [ChainWeights.wordWeight_pred]
  apply Finset.prod_pos
  intro k _
  apply weight_pos
  have hq := (ChainWeights.firstCoordinate s len i k).property
  have hq' := (ChainWeights.nextCoordinate s len i k).property
  simp only [ChainWeights.firstCoordinate_val,block_interval,Finset.mem_Ico] at hq
  simp only [ChainWeights.nextCoordinate_val,block_interval,Finset.mem_Ico] at hq'
  have hh := hw i ((k.val:ℤ)+lower s len i) hq.1 (by omega)
  simpa only [RepeatedBlocks.word,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hh

def bins (w : C → ℤ → Letter) (i : Underlying s len) : ℤ :=
  ⌊-Real.log (wordWeight (height s len i) (RepeatedBlocks.word s len w i))⌋

omit [Fintype C] in
lemma mem_bin (w : C → ℤ → Letter) (hw : ActualStageLabels.Immersed s len w)
    (i : Underlying s len) : RepeatedBlocks.word s len w i ∈ binWords (height s len i) (bins s len w i) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,block_weight_pos s len w hw i,rfl⟩

lemma fullWords_of_comparing {E : Type*} (m : C → ℕ)
    (cmp : Comparisons (E:=E) (RepeatedBlocks.traversalLength len m))
    (j : ℕ) (w : C → ℤ → Letter) (hw : ActualStageLabels.Comparing len m cmp w)
    (hr : ActualStageLabels.Immersed s len w) :
    (fun x : ChainStageLabels.StagePosition len m j => w x.1.val x.2.val) ∈
      ChainStageLabels.fullWords s len m j cmp (bins s len w) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,w,hw,hr,mem_bin s len w hr,rfl⟩

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "lenR" => repLength Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (ChainChunkTransport.color Γ mark h2 paths)

def globalWord (label : D → Types.Letter) (c : R) (q : ℤ) : Letter :=
  Types.signedLetter.symm (label (F^[q.toNat] c.val.val))

lemma immersed (hs : 0<s) (label : D → Types.Letter)
    (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (hinj : ∀ d e,Γ.origin d=Γ.origin e → label d=label e → d=e) :
    ActualStageLabels.Immersed s (lenR) (globalWord Γ mark h2 label) := by
  intro i q hq hq'
  have hb : q∈block s i.2.val := by rw [block_interval s (lenR) i]; simp only [Finset.mem_Ico]; omega
  have hb' : q+1∈block s i.2.val := by rw [block_interval s (lenR) i]; simp only [Finset.mem_Ico]; omega
  have ht := full_subset s hs (lenR i.1) i.2 hb
  have ht' := full_subset s hs (lenR i.1) i.2 hb'
  rw [AffineIntervals.nat_positions,Finset.mem_Ico] at ht ht'
  have hn := normalized_immersed Γ mark h2 Types.inverse label hl hinj i.1 q ht.1 ht'.2
  intro he
  apply hn
  apply Types.signedLetter.symm.injective
  rw [signed_inverse]
  exact he

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

lemma comparing (label : D → Types.Letter)
    (hl : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (hc : ∀ x e,cmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if cmp.reverse e then Types.inverse (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ActualStageLabels.Comparing (lenR) (m)
      ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi) (globalWord Γ mark h2 label) := by
  intro x a ha
  have hh := normalized_compatible Γ mark h2 paths cmp lo hi hlo hhi Types.inverse
    Types.inverse_inverse label hl hc x a ha
  apply_fun Types.signedLetter.symm at hh
  rw [signed_choice] at hh
  have hp : ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).pairing=
      (repeatedChunks Γ mark h2 paths).pairing cmp := rfl
  rw [hp]
  exact hh

end TorsionFreeZeroDivisors.ActualStageFeasibility

namespace TorsionFreeZeroDivisors.StagePartition
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks ChainStageLabels WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)

abbrev CA := {a : C // j < m a ∧ side a=true}
abbrev CB := {b : C // j < m b ∧ side b=false}
abbrev lenA : CA m side j → ℕ := fun a => len a.val
abbrev lenB : CB m side j → ℕ := fun b => len b.val

def restrictA (F : StagePosition len m j → Letter) : Position (lenA len m side j) → Letter :=
  fun x => F ⟨⟨x.1.val,x.1.property.1⟩,x.2⟩
def restrictB (F : StagePosition len m j → Letter) : Position (lenB len m side j) → Letter :=
  fun x => F ⟨⟨x.1.val,x.1.property.1⟩,x.2⟩

def indexA (i : Underlying s (lenA len m side j)) : Underlying s len := ⟨i.1.val,i.2⟩
def indexB (i : Underlying s (lenB len m side j)) : Underlying s len := ⟨i.1.val,i.2⟩

include hs in
theorem binsA (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    ∀ i, word s (lenA len m side j) (StageExpectation.readWord (lenA len m side j)
      (restrictA len m side j F)) i ∈ binWords (height s (lenA len m side j) i) (d (indexA s len m side j i)) := by
  obtain ⟨w,_,_,hb,rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenA len m side j) (StageExpectation.readWord (lenA len m side j)
      (restrictA len m side j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexA s len m side j i) := by
    funext k
    dsimp only [word,StageExpectation.readWord]
    rw [dif_pos (StageExpectation.word_position s hs (lenA len m side j) i k)]
    rfl
  rw [he]
  exact hb (indexA s len m side j i)

include hs in
theorem binsB (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    ∀ i, word s (lenB len m side j) (StageExpectation.readWord (lenB len m side j)
      (restrictB len m side j F)) i ∈ binWords (height s (lenB len m side j) i) (d (indexB s len m side j i)) := by
  obtain ⟨w,_,_,hb,rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenB len m side j) (StageExpectation.readWord (lenB len m side j)
      (restrictB len m side j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexB s len m side j i) := by
    funext k
    dsimp only [word,StageExpectation.readWord]
    rw [dif_pos (StageExpectation.word_position s hs (lenB len m side j) i k)]
    rfl
  rw [he]
  exact hb (indexB s len m side j i)

def joinBlock : Underlying s (lenA len m side j) ⊕ Underlying s (lenB len m side j) →
    Underlying s (StageExpectation.activeLen len m j)
  | .inl i => ⟨⟨i.1.val,i.1.property.1⟩,i.2⟩
  | .inr i => ⟨⟨i.1.val,i.1.property.1⟩,i.2⟩

omit [Fintype C] in
theorem joinBlock_bijective : Function.Bijective (joinBlock s len m side j) := by
  constructor
  · intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        rcases x with ⟨⟨a,ha⟩,ix⟩
        rcases y with ⟨⟨b,hb⟩,iy⟩
        have hab : a=b := congrArg (fun z => z.1.val) he
        subst b
        have hii : ix=iy := Fin.ext (congrArg (fun z => z.2.val) he)
        subst iy
        rfl
      | inr y =>
        have h := congrArg (fun z => side z.1.val) he
        change side x.1.val=side y.1.val at h
        rw [x.1.property.2,y.1.property.2] at h
        cases h
    | inr x =>
      cases y with
      | inl y =>
        have h := congrArg (fun z => side z.1.val) he
        change side x.1.val=side y.1.val at h
        rw [x.1.property.2,y.1.property.2] at h
        cases h
      | inr y =>
        rcases x with ⟨⟨a,ha⟩,ix⟩
        rcases y with ⟨⟨b,hb⟩,iy⟩
        have hab : a=b := congrArg (fun z => z.1.val) he
        subst b
        have hii : ix=iy := Fin.ext (congrArg (fun z => z.2.val) he)
        subst iy
        rfl
  · rintro ⟨⟨c,hc⟩,b⟩
    cases hh : side c with
    | true => exact ⟨.inl ⟨⟨c,hc,hh⟩,b⟩,rfl⟩
    | false => exact ⟨.inr ⟨⟨c,hc,hh⟩,b⟩,rfl⟩

def blockEquiv := Equiv.ofBijective (joinBlock s len m side j) (joinBlock_bijective s len m side j)

theorem bin_sum (d : Underlying s len → ℤ) :
    (∑ i, (d (indexA s len m side j i) : ℝ)) + (∑ i, (d (indexB s len m side j i) : ℝ)) =
      ∑ i ∈ activeBlocks s len m j, (d i : ℝ) := by
  rw [← StageExpectation.active_bin_sum s len m j d]
  calc
    _ = ∑ i : Underlying s (lenA len m side j) ⊕ Underlying s (lenB len m side j),
        (d (StageExpectation.activeIndex s len m j (joinBlock s len m side j i)) : ℝ) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := Fintype.sum_equiv (blockEquiv s len m side j) _ _ (fun _ => rfl)

variable (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)

def sideA : TwoSideStage.Side where
  C := CA m side j; V := VA; TV := TA
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenA len m side j
  first := firstA; last := lastA; outgoing := outA; pin := pinA

def sideB : TwoSideStage.Side where
  C := CB m side j; V := VB; TV := TB
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenB len m side j
  first := firstB; last := lastB; outgoing := outB; pin := pinB

local notation "SA" => sideA len m side j firstA lastA outA pinA
local notation "SB" => sideB len m side j firstB lastB outB pinB

theorem exponential_fusion (u v k x y z : ℝ) (hz : x+y=z) :
    Real.exp (u+v)*(k*Real.exp (-x-y)) = k*Real.exp (u-z+v) := by
  rw [← hz]
  simp only [sub_eq_add_neg,Real.exp_add,Real.exp_neg]
  ring

include hs in
/-- The joint matching expectation applied to the actual fullWords projection,
including cross-side comparisons. All entropy and bin costs are computed on
that one global pattern. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (n p : ℝ) (N D R : ℕ) (hA : TwoSideStage.Conditions SA n p N D R)
    (hB : TwoSideStage.Conditions SB n p N D R) :
    TwoSideMean.mean (((SA).samples N) ×ˢ ((SB).samples N))
      (TwoSideStage.count SA SB (fullWords s len m j cmp d)
        (restrictA len m side j) (restrictB len m side j)) ≤
      ((SA).cost n p R * (SB).cost n p R) *
        Real.exp ((∑ c : StageLabels.activeComponents
          (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
          ActualStageLabels.cost s hs len m cmp err d c.val) -
          (∑ i ∈ activeBlocks s len m j, (d i : ℝ)) +
          (2*(err : ℝ)*Fintype.card (Underlying s len)+(s+1)*Fintype.card C)*
            Real.log (Fintype.card Letter)) := by
  have h := TwoSideStage.mean_bound s hs SA SB (fullWords s len m j cmp d)
    (restrictA len m side j) (restrictB len m side j) n p N D R hA hB
    (fun i => d (indexA s len m side j i)) (fun i => d (indexB s len m side j i))
    (binsA s hs len m side j cmp d) (binsB s hs len m side j cmp d)
  have hc := full_stage_count s hs len m j cmp d err hlarge hscale hreduced
  have hn : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TA)).trans hA.vertices
  have hp := hA.nonneg
  have hcost : 0 ≤ (SA).cost n p R * (SB).cost n p R := by unfold TwoSideStage.Side.cost; positivity
  have h' := h.trans (mul_le_mul_of_nonneg_right hc
    (mul_nonneg hcost (Real.exp_pos _).le))
  exact h'.trans_eq (exponential_fusion _ _ _ _ _ _ (bin_sum s len m side j d))

end TorsionFreeZeroDivisors.StagePartition

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PartitionEntropy
open scoped Classical BigOperators
open StageEntropy BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate StagePartition
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)
variable (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)
local notation "SA" => sideA len m side j firstA lastA outA pinA
local notation "SB" => sideB len m side j firstB lastB outB pinB

/-- A complete literal-stage first moment, with its signed vertex exponent
and the source denominator, without stage independence. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err K Q rep : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep) (hr : 0<StageDenominator.denominator K rep)
    (hA : TwoSideStage.Conditions SA (TypedGraphs.size rep) (129/16513)
      (3*GirthAsymptotics.L (TypedGraphs.size rep)) 132 (StageDenominator.denominator K rep))
    (hB : TwoSideStage.Conditions SB (TypedGraphs.size rep) (129/16513)
      (3*GirthAsymptotics.L (TypedGraphs.size rep)) 132 (StageDenominator.denominator K rep))
    (hlen : ∀ c,0<len c) (hQ : Fintype.card (CA m side j)+Fintype.card (CB m side j)≤Q)
    (hE : (SA).edges+(SB).edges ≤ K*GirthAsymptotics.L (TypedGraphs.size rep)) :
    TwoSideMean.mean (((SA).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))) ×ˢ
      ((SB).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))))
      (TwoSideStage.count SA SB (fullWords s len m j cmp d)
        (restrictA len m side j) (restrictB len m side j)) ≤
      Real.exp (((((SA).freeMarks+(SB).freeMarks:ℕ):ℝ)-
        (Fintype.card (CA m side j)+Fintype.card (CB m side j):ℕ))*Real.log (TypedGraphs.size rep) +
          labelCost s hs len m cmp err d j + looseCost s len err + StageDenominator.error K Q rep) := by
  have hm := StagePartition.mean_bound s hs len m side j firstA lastA firstB lastB
    outA outB pinA pinB cmp d err hlarge hscale hreduced
    (TypedGraphs.size rep) (129/16513) _ 132 _ hA hB
  have hc := StageDenominator.joint_cost_bound SA SB K Q rep hn hr
    (fun c => hlen c.val) (fun c => hlen c.val) hQ hE
  apply hm.trans
  apply (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  unfold labelCost looseCost
  change (((((SA).freeMarks+(SB).freeMarks:ℕ):ℝ)-
    (Fintype.card (CA m side j)+Fintype.card (CB m side j):ℕ))*Real.log (TypedGraphs.size rep)+
      StageDenominator.error K Q rep) + _ = _
  ring

end TorsionFreeZeroDivisors.PartitionEntropy

namespace TorsionFreeZeroDivisors.SideRestriction
open scoped Classical
open PortSubdivision
variable {V D : Type*} (Γ : PortGraph V D) (side : V → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)

variable {QV QD : Type*} (Q : PortGraph QV QD) (fv : QV ↪ V) (fd : QD ↪ D)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d))
    (hf : ∀ v,side (fv v)=b)

def vertex : QV ↪ Vertex side b := ⟨fun v => ⟨fv v,hf v⟩,fun _ _ h => fv.injective (congrArg Subtype.val h)⟩
def dart : QD ↪ Dart Γ side b :=
  ⟨fun d => ⟨fd d,by rw [←ho]; exact hf _⟩,fun _ _ h => fd.injective (congrArg Subtype.val h)⟩

lemma origin_map (d : QD) : vertex side b fv hf (Q.origin d) =
    (graph Γ side hs b).origin (dart Γ side b Q fv fd ho hf d) := by
  exact Subtype.ext (ho d)
include hr in
lemma reverse_map (d : QD) : dart Γ side b Q fv fd ho hf (Q.reverse d) =
    (graph Γ side hs b).reverse (dart Γ side b Q fv fd ho hf d) := by
  exact Subtype.ext (hr d)

variable [Fintype V] [Fintype D] [Fintype QV] [Fintype QD]
    {TV T : Type*} [Fintype TV] [Fintype T]
    (label : D → T) (outgoing : TV → Finset T) (pin : Vertex side b → Option TV)
    (bar : T → T) (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

/-- Restrict a realized prescribed side to an injectively immersed subgraph
whose target vertices really lie on that side. -/
def embedding (e : RealizationTransport.Embedding (graph Γ side hs b) (fun d => label d.val)
    outgoing pin bar r) (pin' : QV → Option TV)
    (hp : ∀ v y,pin' v=some y → pin (vertex side b fv hf v)=some y) :
    RealizationTransport.Embedding Q (label ∘ fd) outgoing pin' bar r :=
  RealizationTransport.restrict e Q (vertex side b fv hf) (dart Γ side b Q fv fd ho hf)
    (origin_map Γ side hs b Q fv fd ho hf) (reverse_map Γ side hs b Q fv fd ho hr hf) pin' hp

end TorsionFreeZeroDivisors.SideRestriction

namespace TorsionFreeZeroDivisors.StageSideEmbedding
open scoped Classical BigOperators
open ChainSubdivision
variable {C V : Type*} (len m : C → ℕ) (j : ℕ) (side : C → Bool) (vside : V → Bool)
    (first last : {c // j < m c} → V)
    (hf : ∀ c,vside (first c)=side c.val) (hl : ∀ c,vside (last c)=side c.val) (b : Bool)

abbrev Chain := {c : C // j < m c ∧ side c=b}
abbrev Vertex := {v : V // vside v=b}
abbrev length : Chain m j side b → ℕ := fun c => len c.val

def firstPoint (c : Chain m j side b) : Vertex vside b :=
  ⟨first ⟨c.val,c.property.1⟩,(hf _).trans c.property.2⟩
def lastPoint (c : Chain m j side b) : Vertex vside b :=
  ⟨last ⟨c.val,c.property.1⟩,(hl _).trans c.property.2⟩
abbrev graph := ChainSubdivision.graph (length len m j side b)
  (firstPoint m j side vside first hf b) (lastPoint m j side vside last hl b)
local notation "Q" => graph len m j side vside first last hf hl b
local notation "P" => ChainSubdivision.graph (StageExpectation.activeLen len m j) first last

def vertex : ChainSubdivision.Vertex (length len m j side b) (V := Vertex vside b) →
    ChainSubdivision.Vertex (StageExpectation.activeLen len m j) (V := V)
  | .inl v => .inl v.val
  | .inr ⟨c,i⟩ => .inr ⟨⟨c.val,c.property.1⟩,i⟩
def dart : ChainSubdivision.Dart (length len m j side b) →
    ChainSubdivision.Dart (StageExpectation.activeLen len m j) :=
  fun d => (⟨⟨d.1.1.val,d.1.1.property.1⟩,d.1.2⟩,d.2)

lemma vertex_injective : Function.Injective (vertex len m j side vside b) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    | inr w => cases h
  | inr v =>
    cases w with
    | inl w => cases h
    | inr w =>
      rcases v with ⟨c,i⟩
      rcases w with ⟨d,k⟩
      have h' := Sum.inr.inj h
      have hcd : c=d := Subtype.ext (congrArg (fun x => x.1.val) h')
      cases hcd
      have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
      cases hik
      rfl

lemma dart_injective : Function.Injective (dart len m j side b) := by
  rintro ⟨⟨c,i⟩,r⟩ ⟨⟨d,k⟩,s⟩ h
  have hrs := congrArg Prod.snd h
  cases hrs
  have h' := congrArg Prod.fst h
  have hcd : c=d := Subtype.ext (congrArg (fun x => x.1.val) h')
  cases hcd
  have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
  cases hik
  rfl

lemma point_map (c : Chain m j side b) (k : Fin (length len m j side b c+1)) :
    vertex len m j side vside b
      (point (length len m j side b) (firstPoint m j side vside first hf b)
        (lastPoint m j side vside last hl b) c k) =
    point (StageExpectation.activeLen len m j) first last ⟨c.val,c.property.1⟩ k := by
  unfold point
  split_ifs <;> rfl

lemma origin_map (d : ChainSubdivision.Dart (length len m j side b)) :
    vertex len m j side vside b ((Q).origin d) = (P).origin (dart len m j side b d) := by
  rcases d with ⟨⟨c,i⟩,r⟩
  cases r
  · simpa only [dart,origin_forward] using
      point_map len m j side vside first last hf hl b c ⟨i.val,by have h:=i.isLt; omega⟩
  · simpa only [dart,origin_backward] using
      point_map len m j side vside first last hf hl b c ⟨i.val+1,by have h:=i.isLt; omega⟩

lemma reverse_map (d : ChainSubdivision.Dart (length len m j side b)) :
    dart len m j side b ((Q).reverse d) = (P).reverse (dart len m j side b d) := rfl

/-- Restriction of a full stage string to this prescribed side. -/
def restrictWord (F : ComparedBlocks.Position (StageExpectation.activeLen len m j) → WordEstimate.Letter) :
    ComparedBlocks.Position (length len m j side b) → WordEstimate.Letter :=
  fun x => F ⟨⟨x.1.val,x.1.property.1⟩,x.2⟩

lemma label_map (F : ComparedBlocks.Position (StageExpectation.activeLen len m j) → WordEstimate.Letter)
    (d : ChainSubdivision.Dart (length len m j side b)) :
    ChainRealization.label (length len m j side b)
      (StageExpectation.readWord (length len m j side b) (restrictWord len m j side b F)) d =
    ChainRealization.label (StageExpectation.activeLen len m j)
      (StageExpectation.readWord (StageExpectation.activeLen len m j) F) (dart len m j side b d) := by
  rcases d with ⟨⟨c,i⟩,r⟩
  cases r <;> rfl

variable [Fintype C] [Fintype V]

/-- Exact partitions; no isolated vertices from inactive stages are introduced. -/
lemma chain_card : Fintype.card (Chain m j side true)+Fintype.card (Chain m j side false)=
    Fintype.card {c // j < m c} := by
  let f : Chain m j side true ⊕ Chain m j side false → {c // j < m c} :=
    Sum.elim (fun c => ⟨c.val,c.property.1⟩) (fun c => ⟨c.val,c.property.1⟩)
  have h : Function.Bijective f := by
    constructor
    · intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : {c // j < m c} => z.val) hxy))
        | inr y =>
          have hv : x.val=y.val := congrArg Subtype.val hxy
          have ht := x.property.2
          rw [hv,y.property.2] at ht
          cases ht
      | inr x =>
        cases y with
        | inl y =>
          have hv : x.val=y.val := congrArg Subtype.val hxy
          have ht := x.property.2
          rw [hv,y.property.2] at ht
          cases ht
        | inr y => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : {c // j < m c} => z.val) hxy))
    · rintro ⟨c,hc⟩
      cases hh : side c with
      | true => exact ⟨.inl ⟨c,hc,hh⟩,rfl⟩
      | false => exact ⟨.inr ⟨c,hc,hh⟩,rfl⟩
  simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.ofBijective f h)

lemma vertex_card : Fintype.card (Vertex vside true)+Fintype.card (Vertex vside false)=Fintype.card V := by
  have h := Fintype.card_subtype_compl (fun v : V => vside v=true)
  have he : {v : V // ¬vside v=true} ≃ Vertex vside false :=
    Equiv.subtypeEquivRight (fun v => by cases vside v <;> simp)
  rw [Fintype.card_congr he] at h
  have heq : Fintype.card {v : V // vside v=true}≤Fintype.card V := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  change Fintype.card {v : V // vside v=true}+_= _
  omega

end TorsionFreeZeroDivisors.StageSideEmbedding

namespace TorsionFreeZeroDivisors.ChainSide
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2

def chain (c : R) : Bool := side (Γ.origin c.val.val)

include hs in
lemma next_side (d : D) : side (Γ.origin (F d))=side (Γ.origin d) := by
  change side (Γ.origin (turn Γ.origin mark h2 (Γ.reverse d)))=side (Γ.origin d)
  rw [turn_origin Γ.origin mark h2]
  exact hs d

include hs in
lemma iterate_side (d : D) (i : ℕ) : side (Γ.origin (F^[i] d))=side (Γ.origin d) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply',next_side Γ mark h2 side hs,ih]

include hs in
lemma suppressed_side (d : {d : D // turn Γ.origin mark h2 d=d}) :
    side ((S).origin ((S).reverse d))=side ((S).origin d) := by
  change side (Γ.origin ((S).reverse d).val)=side (Γ.origin d.val)
  have he := chain_last Γ mark h2 d
  rw [last_iterChain] at he
  rw [←he,hs]
  exact iterate_side Γ mark h2 side hs d.val _

include hs in
lemma last_side (c : R) : side (ChainIsomorphism.last Γ mark h2 c).val=chain Γ mark h2 side c :=
  suppressed_side Γ mark h2 side hs c.val

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "W" => StageSubgraphs.ActiveV (S) (ListStageExponents.mult (S) paths) j
local notation "A" => ChainActiveStages.ActiveChain Γ mark h2 paths j

def vertex (w : W) : Bool := side w.val

lemma active_first (c : A) : vertex Γ mark h2 side paths j (ChainActiveStages.first Γ mark h2 paths j c)=
    chain Γ mark h2 side c.val := rfl
include hs in
lemma active_last (c : A) : vertex Γ mark h2 side paths j (ChainActiveStages.last Γ mark h2 paths j c)=
    chain Γ mark h2 side c.val := last_side Γ mark h2 side hs c.val

include hs in
lemma stage_internal (c : A) (i : Fin (ChainStageEmbedding.length Γ mark h2 paths j c-1)) :
    side (ChainStageEmbedding.vertexMap Γ mark h2 paths j (.inr ⟨c,i⟩))=chain Γ mark h2 side c.val := by
  exact iterate_side Γ mark h2 side hs c.val.val.val (i.val+1)

end TorsionFreeZeroDivisors.ChainSide

namespace TorsionFreeZeroDivisors.ActualSideRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons StageSubgraphs
variable {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ) (b : Bool)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "vs" => ChainSide.vertex Γ mark h2 side paths j
local notation "first" => ChainActiveStages.first Γ mark h2 paths j
local notation "last" => ChainActiveStages.last Γ mark h2 paths j
local notation "hf" => ChainSide.active_first Γ mark h2 side paths j
local notation "hl" => ChainSide.active_last Γ mark h2 side hs paths j
local notation "W" => ActiveV (S) (ListStageExponents.mult (S) paths) j

abbrev length := StageSideEmbedding.length len m j cs b
abbrev Marked := StageSideEmbedding.Vertex vs b
abbrev graph := StageSideEmbedding.graph len m j cs vs first last hf hl b
local notation "Q" => graph Γ mark h2 side hs paths j b
local notation "l" => length Γ mark h2 side paths j b

def vertexMap : ChainSubdivision.Vertex l (V := Marked Γ mark h2 side paths j b) → V :=
  ChainStageEmbedding.vertexMap Γ mark h2 paths j ∘ StageSideEmbedding.vertex len m j cs vs b

def dartMap : ChainSubdivision.Dart l → D :=
  ChainStageEmbedding.dartMap Γ mark h2 paths j ∘ StageSideEmbedding.dart len m j cs b

lemma vertex_injective : Injective (vertexMap Γ mark h2 side paths j b) :=
  (ChainStageEmbedding.vertexMap_injective Γ mark h2 paths j).comp
    (StageSideEmbedding.vertex_injective len m j cs vs b)
lemma dart_injective : Injective (dartMap Γ mark h2 side paths j b) :=
  (ChainStageEmbedding.dartMap_injective Γ mark h2 paths j).comp
    (StageSideEmbedding.dart_injective len m j cs b)

lemma origin_map (d : ChainSubdivision.Dart l) :
    vertexMap Γ mark h2 side paths j b ((Q).origin d)=Γ.origin (dartMap Γ mark h2 side paths j b d) := by
  unfold vertexMap dartMap
  dsimp only [Function.comp_apply]
  rw [StageSideEmbedding.origin_map len m j cs vs first last hf hl b]
  exact ChainStageEmbedding.origin_map Γ mark h2 paths j _

lemma reverse_map (d : ChainSubdivision.Dart l) :
    dartMap Γ mark h2 side paths j b ((Q).reverse d)=Γ.reverse (dartMap Γ mark h2 side paths j b d) := by
  unfold dartMap
  dsimp only [Function.comp_apply]
  rw [StageSideEmbedding.reverse_map len m j cs vs first last hf hl b]
  exact ChainStageEmbedding.reverse_map Γ mark h2 paths j _

include hs in
lemma vertex_side (v : ChainSubdivision.Vertex l (V := Marked Γ mark h2 side paths j b)) :
    side (vertexMap Γ mark h2 side paths j b v)=b := by
  cases v with
  | inl v => exact v.property
  | inr v =>
    rcases v with ⟨c,i⟩
    exact (ChainSide.stage_internal Γ mark h2 side hs paths j ⟨c.val,c.property.1⟩ i).trans c.property.2

def word (label : D → Types.Letter) : ComparedBlocks.Position l → WordEstimate.Letter :=
  StageSideEmbedding.restrictWord len m j cs b (ActualStageRealization.word Γ mark h2 paths j label)

lemma label_eq (label : D → Types.Letter) (hlabel : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (d : ChainSubdivision.Dart l) :
    ChainRealization.label l (StageExpectation.readWord l (word Γ mark h2 side paths j b label)) d =
      label (dartMap Γ mark h2 side paths j b d) := by
  rw [show word Γ mark h2 side paths j b label = StageSideEmbedding.restrictWord len m j cs b
    (ActualStageRealization.word Γ mark h2 paths j label) from rfl,
    StageSideEmbedding.label_map]
  exact ActualStageRealization.label_eq Γ mark h2 paths j label hlabel _

variable [Fintype V] {TV : Type} [Fintype TV]
    (label : D → Types.Letter) (outgoing : TV → Finset Types.Letter)
    (pin : SideRestriction.Vertex side b → Option TV)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse)

/-- The literal realization of this prescribed-side active stage follows from
an actual embedding of the original prescribed side. All labels stay the
restrictions of ONE global word. -/
def embedding (e : RealizationTransport.Embedding (SideRestriction.graph Γ side hs b)
      (fun d => label d.val) outgoing pin Types.inverse r)
    (hlabel : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (pin' : Marked Γ mark h2 side paths j b → Option TV)
    (hp : ∀ v y,pin' v=some y → pin ⟨v.val.val,v.property⟩=some y) :
    RealizationTransport.Embedding (Q)
      (ChainRealization.label l (StageExpectation.readWord l (word Γ mark h2 side paths j b label)))
      outgoing (ChainRealization.pin l pin') Types.inverse r := by
  let fv : ChainSubdivision.Vertex l ↪ V :=
    ⟨vertexMap Γ mark h2 side paths j b,vertex_injective Γ mark h2 side paths j b⟩
  let fd : ChainSubdivision.Dart l ↪ D :=
    ⟨dartMap Γ mark h2 side paths j b,dart_injective Γ mark h2 side paths j b⟩
  have hp' : ∀ v y, ChainRealization.pin l pin' v=some y →
      pin (SideRestriction.vertex side b fv (vertex_side Γ mark h2 side hs paths j b) v)=some y := by
    intro v y hy
    cases v with
    | inl v => exact hp v y hy
    | inr v => cases hy
  exact RealizationTransport.congrLabel
    (SideRestriction.embedding Γ side hs b (Q) fv fd
      (origin_map Γ mark h2 side hs paths j b) (reverse_map Γ mark h2 side hs paths j b)
      (vertex_side Γ mark h2 side hs paths j b) label outgoing pin Types.inverse r e _ hp') _
    (label_eq Γ mark h2 side paths j b label hlabel)

end TorsionFreeZeroDivisors.ActualSideRealization

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical BigOperators
variable {V TA TB : Type*} [Fintype V] (side : V → Bool)

omit [Fintype V] in
lemma root_save (r : Option V) :
    (if (root side r true).isSome then (1:ℤ) else 0) +
      (if (root side r false).isSome then (1:ℤ) else 0) = if r.isSome then 1 else 0 := by
  cases r with
  | none => rfl
  | some v => cases hs : side v <;> simp [root,hs]

lemma free_total (r : Option V) (a : TA) (b : TB) :
    (RootPins.free (root side r true) a : ℤ) + (RootPins.free (root side r false) b : ℤ) =
      Fintype.card V - if r.isSome then 1 else 0 := by
  rw [RootPins.free_cast,RootPins.free_cast]
  have hc := StageSideEmbedding.vertex_card side
  change Fintype.card {v : V // side v=true}+Fintype.card {v : V // side v=false}=Fintype.card V at hc
  have hc' := congrArg (fun n : ℕ => (n:ℤ)) hc
  simp only [Nat.cast_add] at hc'
  have hr := root_save side r
  omega

end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking StageSubgraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "mult" => ListStageExponents.mult (S) paths
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

omit [Fintype V] [Fintype D] in
lemma intervals_card (root : Option P) :
    (Fintype.card {p : P // cyclic root p=false}:ℤ) = if root.isSome then 1 else 0 := by
  cases root with
  | none => simp [cyclic]
  | some p => simp [cyclic]

/-- Only the first stage fixes the marked initial vertex. -/
def vertex (root : Option P) (j : ℕ) : Option (ActiveV (S) mult j) :=
  if h : j=0 then by
    subst j
    exact root.map (ActiveRoot.vertex (S) paths hp)
  else none

omit [Fintype V] in
lemma vertex_isSome (root : Option P) (j : ℕ) :
    (vertex Γ mark h2 paths hp root j).isSome = if j=0 then root.isSome else false := by
  unfold vertex
  split_ifs with hj
  · subst j
    simp
  · rfl

/-- The root split over the two prescribed sides has exactly the source saving. -/
def power (side : ∀ j, ActiveV (S) mult j → Bool) (root : Option P)
    {TA TB : Type} (a : TA) (b : TB) (j : ℕ) : ℤ :=
  (RootPins.free (SidePins.root (side j) (vertex Γ mark h2 paths hp root j) true) a : ℤ)+
  (RootPins.free (SidePins.root (side j) (vertex Γ mark h2 paths hp root j) false) b : ℤ)-
    Fintype.card (ChainActiveStages.ActiveChain Γ mark h2 paths j)

lemma power_eq (side : ∀ j, ActiveV (S) mult j → Bool) (root : Option P)
    {TA TB : Type} (a : TA) (b : TB) (j : ℕ) :
    power Γ mark h2 paths hp side root a b j =
      (Fintype.card (ActiveV (S) mult j):ℤ)-Fintype.card (ChainActiveStages.ActiveChain Γ mark h2 paths j)-
        if j=0 then (Fintype.card {p : P // cyclic root p=false}:ℤ) else 0 := by
  unfold power
  rw [SidePins.free_total,vertex_isSome]
  by_cases hj : j=0
  · simp only [hj,ite_true,intervals_card]
    ring
  · simp [hj]

theorem power_nonpos (side : ∀ j, ActiveV (S) mult j → Bool) (root : Option P)
    {TA TB : Type} (a : TA) (b : TB)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step (S).origin (S).reverse))
    (hclose : ∀ i,cyclic root i=true → ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (S).origin (S).reverse x y)
    (M : ℕ) (hM : 0<M) (hm : ∀ c : R,m c≤M) :
    (∑ j : Fin M, (power Γ mark h2 paths hp side root a b j.val : ℝ)) ≤ 0 := by
  have hz := ChainActiveStages.exponent_nonpos Γ mark h2 paths hp (cyclic root) hc hclose M hM hm
  have he : (∑ j : Fin M,power Γ mark h2 paths hp side root a b j.val) ≤ 0 := by
    simpa [power_eq,ListStageExponents.mult] using hz
  exact_mod_cast he

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
variable {V T : Type*}
lemma pin_some_iff (root : Option V) (target : T) (v : V) (y : T) :
    pin root target v=some y ↔ root=some v ∧ target=y := by
  unfold pin
  split_ifs with h <;> simp [h]
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical
variable {V : Type*} (side : V → Bool)
lemma root_eq_some (r : Option V) (b : Bool) (v : {v : V // side v=b}) :
    root side r b=some v ↔ r=some v.val := by
  cases r with
  | none => simp [root]
  | some w =>
    dsimp only [root,Option.bind_some]
    split_ifs with hw
    · simp only [Option.some.injEq]
      exact Subtype.ext_iff
    · simp only [false_iff,Option.some.injEq]
      intro h
      subst w
      exact hw v.property
end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking StageSubgraphs
variable {V D P : Type} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "mult" => ListStageExponents.mult (S) paths

lemma vertex_source (r : Option P) (j : ℕ) (v : ActiveV (S) mult j)
    (h : vertex Γ mark h2 paths hp r j=some v) : source Γ mark h2 paths hp r=some v.val := by
  unfold vertex at h
  split_ifs at h with hj
  subst j
  rcases Option.map_eq_some_iff.mp h with ⟨p,hp',hv⟩
  subst r
  dsimp only [source,Option.map_some]
  have hval := congrArg Subtype.val hv
  rw [ActiveRoot.vertex_val] at hval
  exact congrArg some hval

variable (side : V → Bool)
lemma pin_compatible (r : Option P) {T : Type} (target : T) (b : Bool) (j : ℕ)
    (v : {v : ActiveV (S) mult j // ChainSide.vertex Γ mark h2 side paths j v=b}) (y : T)
    (h : RootPins.pin
      (SidePins.root (ChainSide.vertex Γ mark h2 side paths j) (vertex Γ mark h2 paths hp r j) b)
      target v=some y) :
    RootPins.pin (SidePins.root side (source Γ mark h2 paths hp r) b) target
      ⟨v.val.val,v.property⟩=some y := by
  rw [RootPins.pin_some_iff] at h ⊢
  refine ⟨?_,h.2⟩
  rw [SidePins.root_eq_some] at h
  rw [SidePins.root_eq_some]
  exact vertex_source Γ mark h2 paths hp r j v.val h.1

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.ActualStagePair
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "first" => ChainActiveStages.first Γ mark h2 paths
local notation "last" => ChainActiveStages.last Γ mark h2 paths
local notation "hf" => ChainSide.active_first Γ mark h2 side paths
local notation "hl" => ChainSide.active_last Γ mark h2 side hsid paths

abbrev pinA (j : ℕ) := RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) true) a
abbrev pinB (j : ℕ) := RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) false) b

abbrev A (j : ℕ) : TwoSideStage.Side :=
  StagePartition.sideA len m cs j
    (firstPoint m j cs (vs j) (first j) (hf j) true)
    (lastPoint m j cs (vs j) (last j) (hl j) true)
    (@Types.outgoingA rep) (pinA Γ mark h2 side paths hp root rep a j)

abbrev B (j : ℕ) : TwoSideStage.Side :=
  StagePartition.sideB len m cs j
    (firstPoint m j cs (vs j) (first j) (hf j) false)
    (lastPoint m j cs (vs j) (last j) (hl j) false)
    (@Types.outgoingB rep) (pinB Γ mark h2 side paths hp root rep b j)
local notation "SA" => A Γ mark h2 side hsid paths hp root rep a
local notation "SB" => B Γ mark h2 side hsid paths hp root rep b

lemma power_eq (j : ℕ) :
    (((SA j).freeMarks+(SB j).freeMarks:ℕ):ℝ)-
      (Fintype.card (SA j).C+Fintype.card (SB j).C:ℕ) =
        (StageRoot.power Γ mark h2 paths hp vs root a b j:ℝ) := by
  have hc := StageSideEmbedding.chain_card m j cs
  unfold StageRoot.power
  dsimp only [TwoSideStage.Side.freeMarks,A,B,StagePartition.sideA,StagePartition.sideB]
  rw [Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_natCast,Int.cast_natCast,
    Nat.cast_add,←hc]
  rfl

lemma edges_eq (j : ℕ) : (SA j).edges+(SB j).edges =
    ∑ c : {c : R // j < m c},len c.val := by
  change (∑ c : {c : R // j < m c ∧ cs c=true},len c.val)+
    (∑ c : {c : R // j < m c ∧ cs c=false},len c.val)=_
  rw [← Finset.sum_subtype (Finset.univ.filter fun c => j < m c ∧ cs c=true) (by simp),
    ← Finset.sum_subtype (Finset.univ.filter fun c => j < m c ∧ cs c=false) (by simp),
    ← Finset.sum_subtype (Finset.univ.filter fun c => j < m c) (by simp)]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  cases cs c <;> simp

lemma edges_bound (j : ℕ) : ((SA j).edges+(SB j).edges:ℝ) ≤ StageMass.totalLength len m := by
  rw [← Nat.cast_add,edges_eq,StageMass.totalLength_eq]
  rw [← Finset.sum_subtype (Finset.univ.filter fun c => j < m c) (by simp)]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · have h : (1:ℝ) ≤ m c := by exact_mod_cast (show 1 ≤ m c by omega)
    nlinarith [show (0:ℝ) ≤ len c from Nat.cast_nonneg (len c)]
  · positivity

variable {E : Type}

def count (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (j : ℕ) : (SA j).Match × (SB j).Match → ℕ :=
  TwoSideStage.count (SA j) (SB j) (ChainStageLabels.fullWords s len m j cmp d)
    (StagePartition.restrictA len m cs j) (StagePartition.restrictB len m cs j)

/-- Restricting actual embeddings on the two prescribed sides witnesses the
joint stage count, with a SINGLE global label projection. -/
theorem count_pos (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (j : ℕ) (label : D → Types.Letter)
    (hlabel : ∀ x,label (Γ.reverse x)=Types.inverse (label x))
    (pinA' : SideRestriction.Vertex side true → Option (Types.VertexA rep))
    (pinB' : SideRestriction.Vertex side false → Option (Types.VertexB rep))
    (r : (SA j).Match × (SB j).Match)
    (eA : RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep) pinA' Types.inverse r.1)
    (eB : RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep) pinB' Types.inverse r.2)
    (hpa : ∀ v y,pinA Γ mark h2 side paths hp root rep a j v=some y → pinA' ⟨v.val.val,v.property⟩=some y)
    (hpb : ∀ v y,pinB Γ mark h2 side paths hp root rep b j v=some y → pinB' ⟨v.val.val,v.property⟩=some y)
    (hw : ActualStageRealization.word Γ mark h2 paths j label ∈ ChainStageLabels.fullWords s len m j cmp d) :
    0<count Γ mark h2 side hsid paths hp root rep a b s cmp d j r := by
  exact TwoSideStage.count_pos (SA j) (SB j) _ _ _ r _ hw
    (ActualSideRealization.embedding Γ mark h2 side hsid paths j true label _ pinA' r.1 eA hlabel _ hpa)
    (ActualSideRealization.embedding Γ mark h2 side hsid paths j false label _ pinB' r.2 eB hlabel _ hpb)

/-- The actual rooted, mixed-side stage first moment, with its exact signed
vertex exponent and the source's common denominator loss. -/
theorem mean_bound (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (hs : 0<s) (j err K Q : ℕ)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep)
    (hr : K*GirthAsymptotics.L (TypedGraphs.size rep)+GirthAsymptotics.exclusion (TypedGraphs.size rep)<
      StageDenominator.carrier rep)
    (hQ : Fintype.card R≤Q)
    (hH : StageMass.totalLength len m ≤ K*(GirthAsymptotics.L (TypedGraphs.size rep):ℝ)) :
    TwoSideMean.mean (((SA j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))) ×ˢ
      ((SB j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))))
      (count Γ mark h2 side hsid paths hp root rep a b s cmp d j) ≤
    Real.exp ((StageRoot.power Γ mark h2 paths hp vs root a b j:ℝ)*Real.log (TypedGraphs.size rep)+
      StageEntropy.labelCost s hs len m cmp err d j+StageEntropy.looseCost s len err+
        StageDenominator.error K Q rep) := by
  have hE : (SA j).edges+(SB j).edges ≤ K*GirthAsymptotics.L (TypedGraphs.size rep) := by
    exact_mod_cast (edges_bound Γ mark h2 side hsid paths hp root rep a b j).trans hH
  have hA := StageDenominator.conditionsA K rep hr (SA j).len (SA j).first (SA j).last (SA j).pin
    ((Nat.le_add_right _ _).trans hE)
  have hB := StageDenominator.conditionsB K rep hr (SB j).len (SB j).first (SB j).last (SB j).pin
    ((Nat.le_add_left _ _).trans hE)
  have hq : Fintype.card (StagePartition.CA m cs j)+Fintype.card (StagePartition.CB m cs j)≤Q := by
    rw [StageSideEmbedding.chain_card]
    apply le_trans _ hQ
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have h := PartitionEntropy.mean_bound s hs len m cs j
    (SA j).first (SA j).last (SB j).first (SB j).last
    (@Types.outgoingA rep) (@Types.outgoingB rep) (SA j).pin (SB j).pin cmp d err K Q rep
    hlarge hscale hreduced hn (Nat.sub_pos_of_lt hr) hA hB
    (fun c => chainLength_pos Γ mark h2 c.val) hq hE
  change TwoSideMean.mean _ (count Γ mark h2 side hsid paths hp root rep a b s cmp d j) ≤
    Real.exp (((((SA j).freeMarks+(SB j).freeMarks:ℕ):ℝ)-
      (Fintype.card (SA j).C+Fintype.card (SB j).C:ℕ))*Real.log (TypedGraphs.size rep)+
      StageEntropy.labelCost s hs len m cmp err d j+StageEntropy.looseCost s len err+
        StageDenominator.error K Q rep) at h
  rw [power_eq] at h
  exact h

end TorsionFreeZeroDivisors.ActualStagePair

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks
private lemma mem_profiles_iff {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)
    (d : Underlying s len → ℤ) :
    d∈BinProfiles.profiles s len ↔ ∀ i,d i∈BinProfiles.values s := by
  unfold BinProfiles.profiles
  exact Fintype.mem_piFinset

variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "SA" => ActualStagePair.A Γ mark h2 side hsid paths hp root rep a
local notation "SB" => ActualStagePair.B Γ mark h2 side hsid paths hp root rep b

lemma samples_eq (j : ℕ) : samples rep =
    (SA j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep)) ×ˢ
      (SB j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep)) := by
  ext r
  dsimp only [ActualStagePair.A,ActualStagePair.B,StagePartition.sideA,StagePartition.sideB,
    TwoSideStage.Side.samples]
  simp only [samples,ConditionedMatchings.Matching.conditioned,
    Finset.mem_product,Finset.mem_filter,Finset.mem_univ,true_and]
  erw [Finset.mem_product]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

/-- Literal realization of an enlarged fixed pattern and its bin profile.
The prescribed-side embeddings are into the actual two independent matchings.
The comparisons refer to normalized traversals of the same suppressed graph. -/
def Occurs (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match rep) : Prop :=
  ∃ label : D → Types.Letter,
    (∀ x,label (Γ.reverse x)=Types.inverse (label x)) ∧
    (∀ x y,Γ.origin x=Γ.origin y → label x=label y → x=y) ∧
    ActualStageLabels.Comparing len m cmp (ActualStageFeasibility.globalWord Γ mark h2 label) ∧
    ActualStageFeasibility.bins s len (ActualStageFeasibility.globalWord Γ mark h2 label)=d ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep)
      (sourcePinA Γ mark h2 side paths hp root rep a) Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep)
      (sourcePinB Γ mark h2 side paths hp root rep b) Types.inverse r.2)

/-- Existence of the actual pattern witnesses every stage count. This does
not posit simultaneous independence of the chain-multiplicity stages. -/
theorem count_pos (s : ℝ) (hs : 0<s) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match rep)
    (hr : Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r) (j : ℕ) :
    0<ActualStagePair.count Γ mark h2 side hsid paths hp root rep a b s cmp d j r := by
  rcases hr with ⟨label,hl,hi,hc,hd,⟨eA⟩,⟨eB⟩⟩
  apply ActualStagePair.count_pos Γ mark h2 side hsid paths hp root rep a b s cmp d j label hl
    _ _ r eA eB
    (StageRoot.pin_compatible Γ mark h2 paths hp side root a true j)
    (StageRoot.pin_compatible Γ mark h2 paths hp side root b false j)
  have hw := ActualStageFeasibility.fullWords_of_comparing s len m cmp j
    (ActualStageFeasibility.globalWord Γ mark h2 label) hc
    (ActualStageFeasibility.immersed s Γ mark h2 hs label hl hi)
  rw [hd] at hw
  exact hw

omit [Fintype V] in
/-- A realizable bin profile automatically has the universal lower and upper
weight bounds; those numerical bounds are not extra assumptions on an event. -/
theorem bin_bounds (s : ℝ) (hs : 0<s) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match rep)
    (hr : Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hscale' : ∀ i,(height s len i:ℝ)≤2*s) :
    (∀ i,(1/600:ℝ)*s/2≤d i) ∧ (∀ i,(d i:ℝ)≤256*s) := by
  rcases hr with ⟨label,hl,hi,_hc,hd,_⟩
  have hb := ActualStageFeasibility.mem_bin s len (ActualStageFeasibility.globalWord Γ mark h2 label)
    (ActualStageFeasibility.immersed s Γ mark h2 hs label hl hi)
  rw [hd] at hb
  have h i := WordEstimate.bin_full_bounds (height s len i) (hlarge i) s (hscale i) (hscale' i)
    (d i) _ (hb i)
  exact ⟨fun i => (h i).1,fun i => (h i).2.1⟩

/-- The unbinned event quantifies no artificial stage data: the bin witness is
forced by the literal label words. -/
def Unbinned (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (r : Match rep) : Prop :=
  ∃ d,Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r

omit [Fintype V] in
lemma occurs_profile (s : ℝ) (hs : 3003≤ s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (d : Underlying s len → ℤ)
    (r : Match rep) (hr : Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r) :
    d∈BinProfiles.profiles s len := by
  classical
  have hh (i : Underlying s len) := BinProfiles.height_bounds s (by linarith) len i
  have hl (i : Underlying s len) : 3002≤height s len i := by
    have h : (3002:ℝ)≤height s len i := by linarith [hh i]
    exact_mod_cast h
  obtain ⟨hlo,hhi⟩ := bin_bounds Γ mark h2 side hsid paths hp root rep a b s (by linarith)
    cmp d r hr hl (fun i => by linarith [hh i]) (fun i => by linarith [hh i])
  apply (mem_profiles_iff s len d).mpr
  intro i
  exact Finset.mem_Icc.mpr ⟨by
    have h : (0:ℝ)≤d i := (by positivity : (0:ℝ)≤(1/600:ℝ)*s/2).trans (hlo i)
    exact_mod_cast h,Int.le_floor.mpr (hhi i)⟩

omit [Fintype V] in
lemma unbinned_iff_profile (s : ℝ) (hs : 3003≤ s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (r : Match rep) :
    Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp r ↔
      ∃ d : {d // d∈BinProfiles.profiles s len},
        Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d.val r := by
  constructor
  · rintro ⟨d,hd⟩
    exact ⟨⟨d,occurs_profile Γ mark h2 side hsid paths hp root rep a b s hs cmp d r hd⟩,hd⟩
  · rintro ⟨d,hd⟩
    exact ⟨d.val,hd⟩

variable [Fintype E]

/-- One genuinely realized fixed-bin pattern is exponentially unlikely.
All numerical stage bounds are derived from its two literal matching means;
no independence between multiplicity stages is asserted. -/
theorem probability_bound (s : ℝ) (hs : 0<s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (d : Underlying s len → ℤ)
    (err K Q M : ℕ) (hM : 0<M) (hm : ∀ c,m c≤M)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hscale' : ∀ i,(height s len i:ℝ)≤2*s)
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep)
    (hr : K*GirthAsymptotics.L (TypedGraphs.size rep)+GirthAsymptotics.exclusion (TypedGraphs.size rep)<
      StageDenominator.carrier rep)
    (hQ : Fintype.card R≤Q)
    (hH : StageMass.totalLength len m ≤ K*(GirthAsymptotics.L (TypedGraphs.size rep):ℝ))
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (hb : (StageMass.uncovered s hs len m cmp err:ℝ) ≤
      StageFusion.epsilon (1/600) 256*StageMass.totalLength len m)
    (he : StageMass.residual (E:=E) s len m err M Q (StageDenominator.error K Q rep) ≤
      StageMass.totalLength len m/4800) :
    (((samples rep).filter (Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-StageMass.totalLength len m/(2400*M)) := by
  by_cases hex : ∃ r,Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r
  · rcases hex with ⟨r,hr'⟩
    obtain ⟨hlow,hhigh⟩ := bin_bounds Γ mark h2 side hsid paths hp root rep a b s hs cmp d
      r hr' hlarge hscale hscale'
    have hpw := StageRoot.power_nonpos Γ mark h2 paths hp vs root a b hc hclose M hM hm
    have hlgn : 0≤Real.log (TypedGraphs.size rep) :=
      Real.log_nonneg (by exact_mod_cast (show 1≤TypedGraphs.size rep by omega))
    have hprod := StageMass.decay s hs len m cmp err M Q hm hQ ν hsmall herr d hlow hhigh
      (Real.log (TypedGraphs.size rep)) (StageDenominator.error K Q rep) hlgn
      (fun j : Fin M => (StageRoot.power Γ mark h2 paths hp vs root a b j.val:ℝ)) hpw hb he
    have h := StageFusion.one_pattern (samples rep) M hM
      (Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d)
      (fun j : Fin M => ActualStagePair.count Γ mark h2 side hsid paths hp root rep a b s cmp d j.val)
      (fun j : Fin M => (StageRoot.power Γ mark h2 paths hp vs root a b j.val:ℝ)*
        Real.log (TypedGraphs.size rep)+StageEntropy.labelCost s hs len m cmp err d j.val+
          (StageEntropy.looseCost s len err+StageDenominator.error K Q rep))
      (StageMass.totalLength len m/2400)
      (fun j r _hr hr' => count_pos Γ mark h2 side hsid paths hp root rep a b s hs cmp d r hr' j.val)
      (fun j => by
        have hmom := ActualStagePair.mean_bound Γ mark h2 side hsid paths hp root rep a b
          s cmp d hs j err K Q hlarge hscale hreduced hn hr hQ hH
        rw [← samples_eq Γ mark h2 side hsid paths hp root rep a b j] at hmom
        convert hmom using 1
        · unfold TwoSideMean.mean
          congr 1
        · congr 1; ring)
      (by simpa only [neg_div] using hprod)
    convert h using 1
    congr 1
    ring
  · have hf : (samples rep).filter (Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d)=∅ := by
      ext r
      simp only [Finset.mem_filter,Finset.notMem_empty,iff_false,not_and]
      exact fun _ => fun hr' => hex ⟨r,hr'⟩
    rw [hf,Finset.card_empty,Nat.cast_zero,zero_div]
    exact (Real.exp_pos _).le

/-- Union over all canonical weight bins of an actual pattern. -/
theorem unbinned_probability_bound (s : ℝ) (hs : 0<s) (hslarge : 3003≤ s)
    (cmp : Comparisons (E:=E) (traversalLength len m))
    (err K Q M : ℕ) (hM : 0<M) (hm : ∀ c,m c≤M)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hscale' : ∀ i,(height s len i:ℝ)≤2*s)
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep)
    (hr : K*GirthAsymptotics.L (TypedGraphs.size rep)+GirthAsymptotics.exclusion (TypedGraphs.size rep)<
      StageDenominator.carrier rep)
    (hQ : Fintype.card R≤Q)
    (hH : StageMass.totalLength len m ≤ K*(GirthAsymptotics.L (TypedGraphs.size rep):ℝ))
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (hb : (StageMass.uncovered s hs len m cmp err:ℝ) ≤
      StageFusion.epsilon (1/600) 256*StageMass.totalLength len m)
    (he : StageMass.residual (E:=E) s len m err M Q (StageDenominator.error K Q rep) ≤
      StageMass.totalLength len m/4800)
    (hpositive : ∀ c,1≤ m c)
    (hbins : Real.log (256*s+1)/s≤1/(4800*M:ℝ)) :
    (((samples rep).filter (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-StageMass.totalLength len m/(4800*M)) := by
  let H := StageMass.totalLength len m
  have hH0 : 0≤H := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsum : (∑ c : R,(len c:ℝ))≤H := by
    unfold H
    rw [StageMass.totalLength_eq]
    apply Finset.sum_le_sum
    intro c _
    have hp : (1:ℝ)≤ m c := by exact_mod_cast hpositive c
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (len c): (0:ℝ)≤len c)
  have hcard : ((BinProfiles.profiles s len).card:ℝ)≤Real.exp (H/(4800*M)) := by
    apply (BinProfiles.cardinal_bound s hs len).trans
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (H/s)*Real.log (256*s+1) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hsum hs.le) (Real.log_nonneg (by linarith))
      _ = H*(Real.log (256*s+1)/s) := by ring
      _ ≤ H*(1/(4800*M)) := mul_le_mul_of_nonneg_left hbins hH0
      _ = H/(4800*M) := by ring
  let Profiles := {d // d∈BinProfiles.profiles s len}
  have hB (d : Profiles) := probability_bound Γ mark h2 side hsid paths hp root rep a b
    s hs cmp d.val err K Q M hM hm hc hclose hlarge hscale hscale' hreduced hn hr hQ hH
    ν hsmall herr hb he
  have hu : (((samples rep).filter
      (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp)).card:ℝ)/(samples rep).card ≤
        ((BinProfiles.profiles s len).card:ℝ)*Real.exp (-H/(2400*M)) := by
    by_cases hsamp : (samples rep).Nonempty
    · have h := StageFusion.pattern_union (samples rep) hsamp
        (fun d : Profiles => Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d.val)
        (Real.exp (-H/(2400*M))) hB
      have heq : (samples rep).filter (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp)=
          (samples rep).filter (fun r => ∃ d : Profiles,
            Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d.val r) := by
        ext r
        simp only [Finset.mem_filter]
        exact and_congr_right (fun _ => unbinned_iff_profile Γ mark h2 side hsid paths hp root rep a b
          s hslarge cmp r)
      rw [heq]
      convert h using 1
      congr 1
      exact_mod_cast (Fintype.card_coe (BinProfiles.profiles s len)).symm
    · have heq := Finset.not_nonempty_iff_eq_empty.mp hsamp
      rw [heq,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,zero_div]
      positivity
  calc
    _ ≤ ((BinProfiles.profiles s len).card:ℝ)*Real.exp (-H/(2400*M)) := hu
    _ ≤ Real.exp (H/(4800*M))*Real.exp (-H/(2400*M)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (-H/(4800*M)) := by rw [←Real.exp_add]; congr 1; ring

end TorsionFreeZeroDivisors.ActualPatternEvent

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternUniform
open scoped Classical Topology BigOperators
open Filter GridAsymptotics GirthAsymptotics TypedGraphs

variable {C E : Type*} [Fintype C] [Fintype E]

theorem Ready.residual {K M Q J rep : ℕ} (h : Ready K M Q J rep)
    (hE : Fintype.card E≤J) (offset : Fin (Fintype.card E) → ℤ)
    (len m : C → ℕ) (hQ : Fintype.card C≤Q)
    (hH : StageMass.totalLength len m≤K*(L (size rep):ℝ))
    (hlo : (L (size rep):ℝ)≤StageMass.totalLength len m) (hpos : ∀ c,1≤ m c) :
    StageMass.residual (E:=E) (chosenScale (Fintype.card E) (L (size rep)) offset) len m
      (letterError (Fintype.card E) (L (size rep)) offset) M Q
      (StageDenominator.error K Q rep)≤StageMass.totalLength len m/4800 := by
  have hh := StageUniform.residual_bound K M Q (L (size rep)) h.1 offset len m hQ hH hpos
    (StageDenominator.error K Q rep)
  have hb := (div_le_iff₀ (show (0:ℝ)<L (size rep) by linarith [h.1])).mp
    (hh.trans (h.2.2.2.2 (Fintype.card E) hE).1)
  linarith

end TorsionFreeZeroDivisors.PatternUniform

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2

/-- The fixed-pattern event before any scale or bins are chosen. -/
def Realized (cmp : Comparisons (E:=E) (traversalLength len m)) (r : Match rep) : Prop :=
  ∃ label : D → Types.Letter,
    (∀ x,label (Γ.reverse x)=Types.inverse (label x)) ∧
    (∀ x y,Γ.origin x=Γ.origin y → label x=label y → x=y) ∧
    ActualStageLabels.Comparing len m cmp (ActualStageFeasibility.globalWord Γ mark h2 label) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep)
      (sourcePinA Γ mark h2 side paths hp root rep a) Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep)
      (sourcePinB Γ mark h2 side paths hp root rep b) Types.inverse r.2)

omit [Fintype V] in
lemma unbinned_iff (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m)) (r : Match rep) :
    Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp r ↔
      Realized Γ mark h2 side hsid paths hp root rep a b cmp r := by
  constructor
  · rintro ⟨d,label,hl,hi,hc,_,ha,hb⟩
    exact ⟨label,hl,hi,hc,ha,hb⟩
  · rintro ⟨label,hl,hi,hc,ha,hb⟩
    exact ⟨_,label,hl,hi,hc,rfl,ha,hb⟩

variable [Fintype E]

def defect (cmp : Comparisons (E:=E) (traversalLength len m)) : ℕ :=
  (Finset.univ.filter (fun x => cmp.pairing.partner x=x)).card

omit [Fintype V] [Fintype E] in
lemma uncovered_eq (s : ℝ) (hs : 0<s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (err : ℕ) :
    StageMass.uncovered s hs len m cmp err=defect Γ mark h2 paths cmp := by
  unfold StageMass.uncovered defect OccurrenceMatching.Data.unpairedPositions
  apply congrArg Finset.card
  exact Finset.filter_congr_decidable _ _ _

/-- Uniform probability bound with no entropy, moment or scale hypothesis.
The ready threshold is independent of all carrier types and pattern data. -/
theorem uniform_probability_bound (K Q M J : ℕ) (hM : 0<M)
    (hready : PatternUniform.Ready K M Q J rep)
    (cmp : Comparisons (E:=E) (traversalLength len m))
    (hm : ∀ c,m c≤M) (hpositive : ∀ c,1≤ m c)
    (hc : ∀ i, List.IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse) (paths i))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hQ : Fintype.card R≤Q) (hE : Fintype.card E≤J)
    (hH : StageMass.totalLength len m ≤ K*(L (size rep):ℝ))
    (hlo : (L (size rep):ℝ)≤StageMass.totalLength len m)
    (hb : (defect Γ mark h2 paths cmp:ℝ)≤
      StageFusion.epsilon (1/600) 256*StageMass.totalLength len m) :
    (((samples rep).filter (Realized Γ mark h2 side hsid paths hp root rep a b cmp)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  let eqv := Fintype.equivFin E
  let off : Fin (Fintype.card E) → ℤ := fun i => cmp.offset (eqv.symm i)
  let s := chosenScale (Fintype.card E) (L (size rep)) off
  let err := letterError (Fintype.card E) (L (size rep)) off
  have hs : 0<s := chosenScale_pos _ hready.1 off
  obtain ⟨hl,he⟩ := (hready.2.2.2.2 (Fintype.card E) hE).2 off
  obtain ⟨ν,hν⟩ := uniform_alignment (Fintype.card E) hready.1 off
  have hν' (e : E) : 2*|(cmp.offset e:ℝ)-(ν (eqv e):ℝ)*s|+4≤err := by
    simpa only [off,Equiv.symm_apply_apply] using hν (eqv e)
  have hh (i : Underlying s len) := BinProfiles.height_bounds s hs.le len i
  have hlarge (i : Underlying s len) : 3002≤height s len i := by
    have h : (3002:ℝ)≤height s len i := by linarith [hh i]
    exact_mod_cast h
  have hres := hready.residual hE off len m hQ hH hlo hpositive
  have hu := unbinned_probability_bound Γ mark h2 side hsid paths hp root rep a b s hs hl cmp
    err K Q M hM hm hc hclose hlarge (fun i => by linarith [hh i])
    (fun i => by linarith [hh i]) hreduced hready.2.1 hready.2.2.1 hQ hH
    (fun e => ν (eqv e)) he hν' (by simpa only [uncovered_eq] using hb) hres hpositive
    ((GridUniform.bin_bound (Fintype.card E) hready.1 off).trans hready.2.2.2.1)
  have heq : (samples rep).filter (Realized Γ mark h2 side hsid paths hp root rep a b cmp)=
      (samples rep).filter (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp) := by
    ext r
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => (unbinned_iff Γ mark h2 side hsid paths hp root rep a b s cmp r).symm)
  rw [heq]
  apply hu.trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg hlo) (by positivity)

end TorsionFreeZeroDivisors.ActualPatternEvent

namespace TorsionFreeZeroDivisors.OriginalPattern
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs ActualPatternEvent
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)

/-- The actual cut comparison data, with its carrier exposed once. -/
def cut (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) : Comparisons (E:=E × RepeatedBlocks.Traversal m × RepeatedBlocks.Traversal m)
    (RepeatedBlocks.traversalLength len m) :=
  (repeatedChunks Γ mark h2 paths).comparisons patCmp lo hi hlo hhi

omit [Fintype V] in
lemma normalized (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) {r : Match rep}
    (h : Realized Γ mark h2 side hsid paths hp root rep a b patCmp r) :
    ActualPatternEvent.Realized Γ mark h2 side hsid paths hp root rep a b
      (cut Γ mark h2 paths patCmp lo hi hlo hhi) r := by
  rcases h with ⟨label,hl,hn,hc,ha,hb⟩
  exact ⟨label,hl,hn,ActualStageFeasibility.comparing Γ mark h2 paths patCmp lo hi hlo hhi label hl hc,ha,hb⟩

omit [Fintype V] in
lemma totalLength_eq : StageMass.totalLength len m =
    ∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ) := by
  have he := Fintype.card_congr (repeatedChunks Γ mark h2 paths).equiv
  rw [position_card,position_card] at he
  change (∑ t : RepeatedBlocks.Traversal m,(len t.1:ℝ))=_
  have hh : (∑ t : RepeatedBlocks.Traversal m,len t.1)=∑ p,pl p := he
  exact_mod_cast hh.trans (Finset.sum_congr rfl (fun p _ => pathLength_eq Γ mark h2 paths p))

omit [Fintype V] in
lemma defect_eq (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) :
    ActualPatternEvent.defect Γ mark h2 paths
      (cut Γ mark h2 paths patCmp lo hi hlo hhi) =
    (Finset.univ.filter (fun x => patCmp.pairing.partner x=x)).card := by
  unfold ActualPatternEvent.defect
  rw [←Fintype.card_subtype,←Fintype.card_subtype]
  exact Fintype.card_congr ((repeatedChunks Γ mark h2 paths).unpairedEquiv patCmp)

variable [Fintype E]

/-- The fixed original-path event has the source exponential bound; cuts and
orientations are deterministic and do not add any probability factor. -/
theorem probability_bound (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) (K Q M J : ℕ) (hM : 0<M)
    (hready : PatternUniform.Ready K M Q J rep)
    (hm : ∀ c,m c≤M) (hpositive : ∀ c,1≤ m c)
    (hc : ∀ i, List.IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse) (paths i))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hreduced : ∀ x e,patCmp.side x=some e →
      originalDart Γ mark h2 paths x≠originalDart Γ mark h2 paths (patCmp.pairing.partner x) ∧
      originalDart Γ mark h2 paths x≠Γ.reverse (originalDart Γ mark h2 paths (patCmp.pairing.partner x)))
    (hQ : Fintype.card R≤Q)
    (hE : Fintype.card E*(Fintype.card (RepeatedBlocks.Traversal m))^2≤J)
    (hH : (∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ)) ≤ K*(L (size rep):ℝ))
    (hlength : (L (size rep):ℝ)≤∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ))
    (hb : ((Finset.univ.filter (fun x => patCmp.pairing.partner x=x)).card:ℝ)≤
      StageFusion.epsilon (1/600) 256*∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ)) :
    (((samples rep).filter (Realized Γ mark h2 side hsid paths hp root rep a b patCmp)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  have he : Fintype.card (E × RepeatedBlocks.Traversal m × RepeatedBlocks.Traversal m)≤J := by
    simpa only [Fintype.card_prod,pow_two,mul_assoc] using hE
  have h := ActualPatternEvent.uniform_probability_bound Γ mark h2 side hsid paths hp root rep a b
    K Q M J hM hready (cut Γ mark h2 paths patCmp lo hi hlo hhi)
    hm hpositive hc hclose (normalized_reduced Γ mark h2 paths patCmp lo hi hlo hhi hreduced) hQ he
    (by rwa [totalLength_eq]) (by rwa [totalLength_eq])
    (by simpa only [defect_eq,totalLength_eq] using hb)
  apply le_trans (b:=(((samples rep).filter (ActualPatternEvent.Realized Γ mark h2 side hsid paths hp root rep a b
      (cut Γ mark h2 paths patCmp lo hi hlo hhi))).card:ℝ)/(samples rep).card) _ h
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro r hr
  obtain ⟨hs,he⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hs,normalized Γ mark h2 side hsid paths hp root rep a b patCmp lo hi hlo hhi he⟩

end TorsionFreeZeroDivisors.OriginalPattern

namespace TorsionFreeZeroDivisors.ComparisonGeometry
open scoped Classical
open BlockAlignment ComparedBlocks ChunkComparisons
variable {P P' E E' : Type*} {len : P → ℕ} {len' : P' → ℕ}

def position (e : P ≃ P') (hl : ∀ p,len p=len' (e p)) : Position len ≃ Position len' :=
  Equiv.sigmaCongr e (fun p => Equiv.subtypeEquivRight (fun q => by rw [hl p]))

structure Iso (C : Comparisons (E:=E) len) (C' : Comparisons (E:=E') len') where
  path : P ≃ P'
  comparison : E ≃ E'
  length_eq : ∀ p,len p=len' (path p)
  flip_eq : ∀ j,comparison (C.flip j)=C'.flip (comparison j)
  source_eq : ∀ j,path (C.source j)=C'.source (comparison j)
  lo_eq : ∀ j,C.lo j=C'.lo (comparison j)
  hi_eq : ∀ j,C.hi j=C'.hi (comparison j)
  reverse_eq : ∀ j,C.reverse j=C'.reverse (comparison j)
  offset_eq : ∀ j,C.offset j=C'.offset (comparison j)

namespace Iso
variable {C : Comparisons (E:=E) len} {C' : Comparisons (E:=E') len'} (f : Iso C C')

lemma side_some (x : Position len) (j : E) :
    C'.side ((position f.path f.length_eq) x)=some (f.comparison j) ↔ C.side x=some j := by
  rw [C'.side_iff,C.side_iff]
  change (f.path x.1=C'.source (f.comparison j) ∧ x.2.val∈positions (C'.lo (f.comparison j)) (C'.hi (f.comparison j))) ↔ _
  rw [←f.source_eq,←f.lo_eq,←f.hi_eq,f.path.injective.eq_iff]

lemma side_eq (x : Position len) :
    C'.side ((position f.path f.length_eq) x)=(C.side x).map f.comparison := by
  cases h : C.side x with
  | some j => simpa only [Option.map_some] using (f.side_some x j).mpr h
  | none =>
    simp only [Option.map_none]
    cases h' : C'.side ((position f.path f.length_eq) x) with
    | none => rfl
    | some j =>
      have hh := (f.side_some x (f.comparison.symm j)).mp (by simpa only [Equiv.apply_symm_apply] using h')
      rw [h] at hh
      contradiction

lemma partner_eq (x : Position len) :
    position f.path f.length_eq (C.pairing.partner x)=
      C'.pairing.partner (position f.path f.length_eq x) := by
  cases h : C.side x with
  | none =>
    have h' : C'.side (position f.path f.length_eq x)=none := by rw [f.side_eq,h]; rfl
    rw [(C.none_iff x).mp h,(C'.none_iff _).mp h']
  | some j =>
    have h' := (f.side_some x j).mpr h
    apply position_ext
    · change f.path (C.pairing.partner x).1=_
      rw [C.partner_source _ _ h,C'.partner_source _ _ h',←f.flip_eq,f.source_eq]
    · change (C.pairing.partner x).2.val=_
      rw [C.partner_coordinate _ _ h,C'.partner_coordinate _ _ h',f.reverse_eq,f.offset_eq]
      rfl

end Iso
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.PortSubdivision
structure Iso {V D V' D' : Type*} (Γ : PortGraph V D) (Γ' : PortGraph V' D') where
  vertex : V ≃ V'
  dart : D ≃ D'
  origin_eq : ∀ d,vertex (Γ.origin d)=Γ'.origin (dart d)
  reverse_eq : ∀ d,dart (Γ.reverse d)=Γ'.reverse (dart d)

namespace Iso
variable {V D V' D' V'' D'' : Type*} {Γ : PortGraph V D} {Γ' : PortGraph V' D'} {Γ'' : PortGraph V'' D''}
def symm (f : Iso Γ Γ') : Iso Γ' Γ where
  vertex := f.vertex.symm
  dart := f.dart.symm
  origin_eq d := by
    apply f.vertex.injective
    simp only [Equiv.apply_symm_apply,f.origin_eq]
  reverse_eq d := by
    apply f.dart.injective
    simp only [Equiv.apply_symm_apply,f.reverse_eq]

def trans (f : Iso Γ Γ') (g : Iso Γ' Γ'') : Iso Γ Γ'' where
  vertex := f.vertex.trans g.vertex
  dart := f.dart.trans g.dart
  origin_eq d := by simp only [Equiv.trans_apply,f.origin_eq,g.origin_eq]
  reverse_eq d := by simp only [Equiv.trans_apply,f.reverse_eq,g.reverse_eq]
end Iso
end TorsionFreeZeroDivisors.PortSubdivision

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision.Iso
open scoped Classical
variable {V D V' D' T TV : Type*} [Fintype V] [Fintype D] [Fintype V'] [Fintype D']
    [Fintype T] [Fintype TV] {Γ : PortGraph V D} {Γ' : PortGraph V' D'}
    (f : Iso Γ Γ') (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v,side v=side' (f.vertex v)) (b : Bool)
    (root : Option V) (root' : Option V') (hroot : root.map f.vertex=root')
    (label : D' → T) (outgoing : TV → Finset T) (target : TV) (bar : T → T)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

/-- A side-preserving graph isomorphism transports the actual rooted embedding,
not just its edge or vertex counts. -/
def sideEmbedding (e : RealizationTransport.Embedding (SideRestriction.graph Γ' side' hs' b)
    (fun d => label d.val) outgoing (RootPins.pin (SidePins.root side' root' b) target) bar r) :
    RealizationTransport.Embedding (SideRestriction.graph Γ side hs b)
      (fun d => label (f.dart d.val)) outgoing (RootPins.pin (SidePins.root side root b) target) bar r := by
  let fv : SideRestriction.Vertex side b ↪ SideRestriction.Vertex side' b :=
    ⟨fun v => ⟨f.vertex v.val,(hside v.val).symm.trans v.property⟩,
      fun _ _ h => Subtype.ext (f.vertex.injective (congrArg Subtype.val h))⟩
  let fd : SideRestriction.Dart Γ side b ↪ SideRestriction.Dart Γ' side' b :=
    ⟨fun d => ⟨f.dart d.val,by rw [←f.origin_eq,←hside]; exact d.property⟩,
      fun _ _ h => Subtype.ext (f.dart.injective (congrArg Subtype.val h))⟩
  have ho d : fv ((SideRestriction.graph Γ side hs b).origin d)=
      (SideRestriction.graph Γ' side' hs' b).origin (fd d) := Subtype.ext (f.origin_eq d.val)
  have hr d : fd ((SideRestriction.graph Γ side hs b).reverse d)=
      (SideRestriction.graph Γ' side' hs' b).reverse (fd d) := Subtype.ext (f.reverse_eq d.val)
  have hp v y : RootPins.pin (SidePins.root side root b) target v=some y →
      RootPins.pin (SidePins.root side' root' b) target (fv v)=some y := by
    simp only [RootPins.pin_some_iff,SidePins.root_eq_some]
    rintro ⟨hv,hy⟩
    refine ⟨?_,hy⟩
    rw [←hroot,hv]
    rfl
  exact RealizationTransport.restrict e _ fv fd ho hr _ hp

end TorsionFreeZeroDivisors.PortSubdivision.Iso

namespace TorsionFreeZeroDivisors.OriginalPatternIso
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
variable {V D P E V' D' P' E' : Type} [Fintype V] [Fintype D] [Fintype P]
    [Fintype V'] [Fintype D'] [Fintype P']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (paths' : P' → List {x : D' // turn Γ'.origin mark' h2' x=x}) (hp' : ∀ p,paths' p≠[])
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)
local notation "pl'" => pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths')
variable (f : Iso Γ Γ') (eP : P ≃ P')
    (hwords : ∀ p,((paths p).flatMap (word Γ mark h2)).map f.dart =
      (paths' (eP p)).flatMap (word Γ' mark' h2'))

include hwords in
omit [Fintype V] [Fintype V'] [Fintype P] [Fintype P'] in
lemma length_eq (p : P) : pl p=pl' (eP p) := by
  rw [pathLength_eq,pathLength_eq,←hwords,List.length_map]

include hwords in
omit [Fintype V] [Fintype V'] [Fintype P] [Fintype P'] in
lemma dart_eq (x : Position pl) (hlen : ∀ p,pl p=pl' (eP p)) :
    f.dart (originalDart Γ mark h2 paths x)=
      originalDart Γ' mark' h2' paths' (ComparisonGeometry.position eP hlen x) := by
  apply Option.some.inj
  have h := congrArg (fun l : List D' => l[x.2.val.toNat]?) (hwords x.1)
  rw [List.getElem?_map,originalDart_get] at h
  change some (f.dart (originalDart Γ mark h2 paths x))=_ at h
  rw [←originalDart_get]
  exact h

variable (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v,side v=side' (f.vertex v))
    (root : Option P) (root' : Option P')
    (hroot : (StageRoot.source Γ mark h2 paths hp root).map f.vertex=
      StageRoot.source Γ' mark' h2' paths' hp' root')
    (C : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (C' : Comparisons (E:=E') (pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths')))
    (g : ComparisonGeometry.Iso C C') (hg : g.path=eP)
    (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)

include hwords hside hroot hg in
omit [Fintype V] [Fintype V'] [Fintype P] [Fintype P'] in
/-- An unlabeled pattern isomorphism preserves the actual event in each fixed
sample. No independence or expected-count assumption is used in this bridge. -/
lemma realized (r : Match rep)
    (he : OriginalPattern.Realized Γ' mark' h2' side' hs' paths' hp' root' rep a b C' r) :
    OriginalPattern.Realized Γ mark h2 side hs paths hp root rep a b C r := by
  subst eP
  rcases he with ⟨label,hl,hi,hc,⟨ea⟩,⟨eb⟩⟩
  refine ⟨label ∘ f.dart,?_,?_,?_,?_,?_⟩
  · intro d
    dsimp only [Function.comp_apply]
    rw [f.reverse_eq,hl]
  · intro d e ho he
    apply f.dart.injective
    apply hi _ _ _ he
    rw [←f.origin_eq,←f.origin_eq,ho]
  · intro x j hj
    have hh := hc (ComparisonGeometry.position g.path g.length_eq x) (g.comparison j)
      ((g.side_some x j).mpr hj)
    dsimp only [Function.comp_apply]
    rw [dart_eq Γ mark h2 Γ' mark' h2' paths paths' f g.path hwords x g.length_eq,
      dart_eq Γ mark h2 Γ' mark' h2' paths paths' f g.path hwords (C.pairing.partner x) g.length_eq,
      g.partner_eq,g.reverse_eq]
    exact hh
  · exact ⟨f.sideEmbedding side side' hs hs' hside true _ _ hroot label _ a Types.inverse r.1 ea⟩
  · exact ⟨f.sideEmbedding side side' hs hs' hside false _ _ hroot label _ b Types.inverse r.2 eb⟩

end TorsionFreeZeroDivisors.OriginalPatternIso

/-!
Finite names for the actual-image patterns in entropy.tex 126–138.  The bounds
R,K,T,I are fixed before H grows.  No vertex names or letters are stored.  Raw
codes include invalid multigraphs as an overcount; all validity conditions must
still be checked when a code is used in a realization event.
-/
namespace TorsionFreeZeroDivisors.PatternCoding

section
open scoped BigOperators Classical

/-- A list of at most T chain darts can be stored in T option-valued slots. -/
def packList {A : Type*} (T : ℕ) (p : List A) : Fin T → Option A :=
  fun i => p[i.val]?

lemma packList_injective {A : Type*} (T : ℕ) :
    Function.Injective (fun p : {p : List A // p.length ≤ T} => packList T p.val) := by
  intro p q h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < T
  · exact congrFun h ⟨i,hi⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- One interval uses one path index and two integer endpoints. -/
abbrev Interval (K H : ℕ) := Fin K × Fin (H+1) × Fin (H+1)

/-- Two intervals and their comparison sign. Inactive comparison slots are absent. -/
abbrev Comparison (K H : ℕ) := Option (Interval K H × Interval K H × Bool)

/-- Bounded path sequences, marked graph incidence/reversal, lengths, sides,
root designation and interval data. Unused graph indices may be padded.
The use of oriented darts avoids choosing orientations of loop chains. -/
abbrev Code (R K T I H : ℕ) :=
  (Fin R → Fin R) × (Fin R → Fin R) × (Fin R → Bool) ×
  (Fin R → Fin (H+1)) × (Fin K → Fin T → Option (Fin R)) ×
  Option (Fin K × Bool) × (Fin I → Comparison K H)

lemma card_code (R K T I H : ℕ) :
    Fintype.card (Code R K T I H) =
      R^(2*R) * 2^R * (H+1)^R * (R+1)^(T*K) * (1+2*K) *
      (1+2*K^2*(H+1)^4)^I := by
  simp only [Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,Fintype.card_option]
  simp only [pow_mul]
  ring

lemma card_code_polynomial (R K T I H : ℕ) :
    Fintype.card (Code R K T I H) ≤ coefficient R K T I * (H+1)^(R+4*I) := by
  rw [card_code]
  have hp : 1 ≤ (H+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hh : 1+2*K^2*(H+1)^4 ≤ (1+2*K^2)*(H+1)^4 := by nlinarith
  have he := Nat.pow_le_pow_left hh I
  calc
    _ ≤ R^(2*R)*2^R*(H+1)^R*(R+1)^(T*K)*(1+2*K)*
        ((1+2*K^2)*(H+1)^4)^I := Nat.mul_le_mul_left _ he
    _ = coefficient R K T I*(H+1)^(R+4*I) := by
      simp only [coefficient,mul_pow,pow_add,pow_mul]
      ring

/-- The canonical renaming is independent of every target vertex name. -/
def names {A : Type*} [Fintype A] (R : ℕ) (h : Fintype.card A ≤ R) : A ↪ Fin R :=
  (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb h)

lemma names_injective {A : Type*} [Fintype A] {R : ℕ} (h : Fintype.card A ≤ R) :
    Function.Injective (names R h) := (names R h).injective

/-- Padding a finite table loses none of its entries. -/
def pad {A B : Type*} [Fintype A] (R : ℕ) (_h : Fintype.card A ≤ R)
    (default : B) (f : A → B) (i : Fin R) : B :=
  if hi : i.val < Fintype.card A then f ((Fintype.equivFin A).symm ⟨i.val,hi⟩)
  else default

lemma pad_names {A B : Type*} [Fintype A] (R : ℕ) (h : Fintype.card A ≤ R)
    (default : B) (f : A → B) (a : A) :
    pad R h default f (names R h a) = f a := by
  simp only [pad,names,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Fin.castLEEmb_apply]
  simp

/-- An actual comparison endpoint. Its path and integer position are retained. -/
structure ActualInterval (P : Type*) (H : ℕ) where
  path : P
  start : Fin (H+1)
  stop : Fin (H+1)

/-- The sign records translation versus reflection, not a chosen graph label. -/
structure ActualComparison (P : Type*) (H : ℕ) where
  left : ActualInterval P H
  right : ActualInterval P H
  sign : Bool

def intervalName {P : Type*} [Fintype P] (K H : ℕ) (hP : Fintype.card P ≤ K)
    (a : ActualInterval P H) : Interval K H :=
  (names K hP a.path,a.start,a.stop)

def comparisonName {P : Type*} [Fintype P] (K H : ℕ) (hP : Fintype.card P ≤ K)
    (a : ActualComparison P H) : Comparison K H :=
  some (intervalName K H hP a.left,intervalName K H hP a.right,a.sign)

/-- Explicit encoding of all source pattern data after suppression. The graph
and path carriers can be arbitrary finite types: their old vertex names do
not survive. Empty padding is not counted as an actual chain or path. -/
def encode {D V P J : Type*} [Fintype D] [Fintype V] [Fintype P] [Fintype J]
    (R K T I H : ℕ) (hR : 0<R)
    (hD : Fintype.card D ≤ R) (hV : Fintype.card V ≤ R)
    (hP : Fintype.card P ≤ K) (hJ : Fintype.card J ≤ I)
    (rev : D → D) (origin : D → V) (side : D → Bool)
    (length : D → Fin (H+1)) (paths : P → List D)
    (root : Option (P × Bool)) (comparisons : J → ActualComparison P H) : Code R K T I H :=
  (pad R hD ⟨0,hR⟩ (fun d => names R hD (rev d)),
   pad R hD ⟨0,hR⟩ (fun d => names R hV (origin d)),
   pad R hD false side,
   pad R hD 0 length,
   pad K hP (fun _ => none) (fun p => packList T ((paths p).map (names R hD))),
   root.map (fun a => (names K hP a.1,a.2)),
   pad I hJ none (fun j => comparisonName K H hP (comparisons j)))

end

open scoped Classical

/-- Carrier counts distinguish inactive padding from actual graph indices.
The four extra counts are uniformly bounded, independent of H and n. -/
abbrev SizedCode (R K T I H : ℕ) :=
  Fin (R+1) × Fin (R+1) × Fin (K+1) × Fin (I+1) × Code R K T I H

theorem card_sizedCode (R K T I H : ℕ) :
    Fintype.card (SizedCode R K T I H) ≤
      (R+1)^2*(K+1)*(I+1)*coefficient R K T I*(H+1)^(R+4*I) := by
  have hcard : Fintype.card (SizedCode R K T I H) =
      (R+1)*(R+1)*(K+1)*(I+1)*Fintype.card (Code R K T I H) := by
    simp only [SizedCode,Fintype.card_prod,Fintype.card_fin]
    ring
  rw [hcard]
  have h := Nat.mul_le_mul_left ((R+1)*(R+1)*(K+1)*(I+1))
    (card_code_polynomial R K T I H)
  convert h using 1; ring

variable {A B : Type*} [Fintype A] [Fintype B]

def rename (h : Fintype.card A=Fintype.card B) : A ≃ B :=
  (Fintype.equivFin A).trans ((finCongr h).trans (Fintype.equivFin B).symm)

theorem rename_rank (h : Fintype.card A=Fintype.card B) (a : A) :
    (Fintype.equivFin B (rename h a)).val = (Fintype.equivFin A a).val := by
  simp [rename]

theorem rename_names (R : ℕ) (hA : Fintype.card A ≤ R) (hB : Fintype.card B ≤ R)
    (h : Fintype.card A=Fintype.card B) (a : A) : names R hB (rename h a)=names R hA a := by
  apply Fin.ext
  exact rename_rank h a

theorem same_pad {X : Type*} (R : ℕ) (hA : Fintype.card A ≤ R) (hB : Fintype.card B ≤ R)
    (h : Fintype.card A=Fintype.card B) (x : X) (f : A → X) (g : B → X)
    (he : pad R hA x f=pad R hB x g) (a : A) : f a=g (rename h a) := by
  have hh := congrFun he (names R hA a)
  rw [pad_names,←rename_names R hA hB h,pad_names] at hh
  exact hh

/-- All non-label data of a bounded actual pattern. Proof fields are not
encoded, while all data fields are. -/
structure Data (D V P J : Type*) (T H : ℕ) where
  reverse : D → D
  origin : D → V
  side : D → Bool
  length : D → Fin (H+1)
  paths : P → List D
  path_bound : ∀ p,(paths p).length ≤ T
  root : Option (P × Bool)
  comparisons : J → ActualComparison P H

variable {D V P J D' V' P' J' : Type*}
  [Fintype D] [Fintype V] [Fintype P] [Fintype J]
  [Fintype D'] [Fintype V'] [Fintype P'] [Fintype J']

/-- Exact simultaneous equivalence of graph incidence, orientation, side,
length, every path traversal, root path, and comparison intervals. -/
structure Isomorphism {T H : ℕ} (a : Data D V P J T H) (b : Data D' V' P' J' T H) where
  dart : D ≃ D'
  vertex : V ≃ V'
  path : P ≃ P'
  comparison : J ≃ J'
  reverse_eq : ∀ d,dart (a.reverse d)=b.reverse (dart d)
  origin_eq : ∀ d,vertex (a.origin d)=b.origin (dart d)
  side_eq : ∀ d,a.side d=b.side (dart d)
  length_eq : ∀ d,a.length d=b.length (dart d)
  paths_eq : ∀ p,(a.paths p).map dart=b.paths (path p)
  root_eq : a.root.map (fun x => (path x.1,x.2))=b.root
  comparison_left_path : ∀ j,path (a.comparisons j).left.path=(b.comparisons (comparison j)).left.path
  comparison_left_start : ∀ j,(a.comparisons j).left.start=(b.comparisons (comparison j)).left.start
  comparison_left_stop : ∀ j,(a.comparisons j).left.stop=(b.comparisons (comparison j)).left.stop
  comparison_right_path : ∀ j,path (a.comparisons j).right.path=(b.comparisons (comparison j)).right.path
  comparison_right_start : ∀ j,(a.comparisons j).right.start=(b.comparisons (comparison j)).right.start
  comparison_right_stop : ∀ j,(a.comparisons j).right.stop=(b.comparisons (comparison j)).right.stop
  comparison_sign : ∀ j,(a.comparisons j).sign=(b.comparisons (comparison j)).sign

variable (R K T I H : ℕ) (hR : 0<R)
  (hD : Fintype.card D ≤ R) (hV : Fintype.card V ≤ R)
  (hP : Fintype.card P ≤ K) (hJ : Fintype.card J ≤ I)

def encodeData (a : Data D V P J T H) : SizedCode R K T I H :=
  (⟨Fintype.card D,by omega⟩,⟨Fintype.card V,by omega⟩,
   ⟨Fintype.card P,by omega⟩,⟨Fintype.card J,by omega⟩,
   encode R K T I H hR hD hV hP hJ a.reverse a.origin a.side a.length a.paths a.root a.comparisons)

variable (hD' : Fintype.card D' ≤ R) (hV' : Fintype.card V' ≤ R)
  (hP' : Fintype.card P' ≤ K) (hJ' : Fintype.card J' ≤ I)

/-- Equality of the finite code loses no pattern information: the resulting
isomorphism is valid for loops, repeated paths, and repeated comparisons. -/
theorem same_code_canonical_isomorphism (a : Data D V P J T H) (b : Data D' V' P' J' T H)
    (cD : Fintype.card D=Fintype.card D') (cV : Fintype.card V=Fintype.card V')
    (cP : Fintype.card P=Fintype.card P') (cJ : Fintype.card J=Fintype.card J')
    (he : encode R K T I H hR hD hV hP hJ a.reverse a.origin a.side a.length a.paths a.root a.comparisons =
      encode R K T I H hR hD' hV' hP' hJ' b.reverse b.origin b.side b.length b.paths b.root b.comparisons) :
    ∃ f : Isomorphism a b, f.dart=rename cD ∧ f.path=rename cP ∧ f.vertex=rename cV := by
  simp only [encode,Prod.mk.injEq] at he
  obtain ⟨hr,ho,hs,hl,hp,hroot,hcomp⟩ := he
  have hrev (d : D) : rename cD (a.reverse d)=b.reverse (rename cD d) := by
    apply names_injective hD'
    rw [rename_names R hD hD']
    exact same_pad R hD hD' cD (⟨0,hR⟩ : Fin R) _ _ hr d
  have horig (d : D) : rename cV (a.origin d)=b.origin (rename cD d) := by
    apply names_injective hV'
    rw [rename_names R hV hV']
    exact same_pad R hD hD' cD (⟨0,hR⟩ : Fin R) _ _ ho d
  have hpath (p : P) : (a.paths p).map (rename cD)=b.paths (rename cP p) := by
    have hh := same_pad K hP hP' cP (fun _ => none) _ _ hp p
    have hn : (a.paths p).map (names R hD)=(b.paths (rename cP p)).map (names R hD') := by
      exact congrArg Subtype.val (packList_injective T
        (a₁ := ⟨_,by simpa using a.path_bound p⟩)
        (a₂ := ⟨_,by simpa using b.path_bound (rename cP p)⟩) hh)
    apply (names_injective hD').list_map
    rw [List.map_map]
    have hrn : (names R hD') ∘ (rename cD)=names R hD := by
      funext d
      exact rename_names R hD hD' cD d
    rw [hrn]
    exact hn
  have hroot' : a.root.map (fun x => (rename cP x.1,x.2))=b.root := by
    cases ha : a.root with
    | none =>
      cases hb : b.root with
      | none => rfl
      | some y => simp [ha,hb] at hroot
    | some x =>
      cases hb : b.root with
      | none => simp [ha,hb] at hroot
      | some y =>
        have hh : names K hP x.1=names K hP' y.1 ∧ x.2=y.2 := by
          simpa only [ha,hb,Option.map_some,Option.some.injEq,Prod.mk.injEq] using hroot
        simp only [Option.map_some,Option.some.injEq]
        apply Prod.ext
        · apply names_injective hP'
          rw [rename_names K hP hP']
          exact hh.1
        · exact hh.2
  have hc (j : J) :
      (rename cP (a.comparisons j).left.path=(b.comparisons (rename cJ j)).left.path) ∧
      (a.comparisons j).left.start=(b.comparisons (rename cJ j)).left.start ∧
      (a.comparisons j).left.stop=(b.comparisons (rename cJ j)).left.stop ∧
      (rename cP (a.comparisons j).right.path=(b.comparisons (rename cJ j)).right.path) ∧
      (a.comparisons j).right.start=(b.comparisons (rename cJ j)).right.start ∧
      (a.comparisons j).right.stop=(b.comparisons (rename cJ j)).right.stop ∧
      (a.comparisons j).sign=(b.comparisons (rename cJ j)).sign := by
    have hh := same_pad I hJ hJ' cJ none _ _ hcomp j
    simp only [comparisonName,intervalName,Option.some.injEq,Prod.mk.injEq] at hh
    obtain ⟨⟨h1,h2,h3⟩,⟨h4,h5,h6⟩,h7⟩ := hh
    refine ⟨?_,h2,h3,?_,h5,h6,h7⟩
    · apply names_injective hP'
      rw [rename_names K hP hP']
      exact h1
    · apply names_injective hP'
      rw [rename_names K hP hP']
      exact h4
  exact ⟨⟨rename cD,rename cV,rename cP,rename cJ,hrev,horig,
    same_pad R hD hD' cD false a.side b.side hs,
    same_pad R hD hD' cD 0 a.length b.length hl,hpath,hroot',
    (fun j => (hc j).1),(fun j => (hc j).2.1),(fun j => (hc j).2.2.1),
    (fun j => (hc j).2.2.2.1),(fun j => (hc j).2.2.2.2.1),
    (fun j => (hc j).2.2.2.2.2.1),(fun j => (hc j).2.2.2.2.2.2)⟩, rfl, rfl, rfl⟩

end TorsionFreeZeroDivisors.PatternCoding

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ComparisonCoding
open scoped Classical
open PatternCoding

/-- Full integer affine comparison geometry. The offset uses [-2H,2H]. -/
structure Data (P E : Type*) (H : ℕ) where
  flip : E → E
  source : E → P
  lower : E → Fin (H+1)
  upper : E → Fin (H+1)
  reverse : E → Bool
  offset : E → Fin (4*H+1)

abbrev Code (K I H : ℕ) := (Fin I → Fin I) × (Fin I → Fin K) ×
  (Fin I → Fin (H+1)) × (Fin I → Fin (H+1)) ×
  (Fin I → Bool) × (Fin I → Fin (4*H+1))

lemma card_code (K I H : ℕ) : Fintype.card (Code K I H) =
    I^I*K^I*(H+1)^(2*I)*2^I*(4*H+1)^I := by
  simp only [Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [show 2*I=I+I by omega, pow_add]
  ring

lemma card_code_bound (K I H : ℕ) : Fintype.card (Code K I H) ≤
    coefficient K I*(H+1)^(3*I) := by
  rw [card_code]
  have h : (4*H+1)^I≤(4*(H+1))^I := Nat.pow_le_pow_left (by omega) I
  apply le_trans (Nat.mul_le_mul_left _ h)
  apply le_of_eq
  simp only [coefficient,mul_pow,show 2*I=I+I by omega,
    show 3*I=I+(I+I) by omega,pow_add]
  rw [show (8:ℕ)^I=2^I*4^I by rw [←mul_pow]; norm_num]
  ring

variable {P E P' E' : Type*} [Fintype P] [Fintype E] [Fintype P'] [Fintype E']
    (K I H : ℕ) (hK : 0<K) (hI : 0<I)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

def encode (a : Data P E H) : Code K I H :=
  (pad I hE ⟨0,hI⟩ (fun e => names I hE (a.flip e)),
   pad I hE ⟨0,hK⟩ (fun e => names K hP (a.source e)),
   pad I hE 0 a.lower,pad I hE 0 a.upper,
   pad I hE false a.reverse,pad I hE 0 a.offset)

structure Isomorphism (a : Data P E H) (b : Data P' E' H) where
  path : P ≃ P'
  comparison : E ≃ E'
  flip_eq : ∀ e,comparison (a.flip e)=b.flip (comparison e)
  source_eq : ∀ e,path (a.source e)=b.source (comparison e)
  lower_eq : ∀ e,a.lower e=b.lower (comparison e)
  upper_eq : ∀ e,a.upper e=b.upper (comparison e)
  reverse_eq : ∀ e,a.reverse e=b.reverse (comparison e)
  offset_eq : ∀ e,a.offset e=b.offset (comparison e)

variable (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

theorem encode_complete (a : Data P E H) (b : Data P' E' H)
    (cP : Fintype.card P=Fintype.card P') (cE : Fintype.card E=Fintype.card E')
    (he : encode K I H hK hI hP hE a=encode K I H hK hI hP' hE' b) :
    ∃ f : Isomorphism H a b, f.path=rename cP ∧ f.comparison=rename cE := by
  simp only [encode,Prod.mk.injEq] at he
  obtain ⟨hf,hs,hl,hu,hr,ho⟩ := he
  have hflip (e : E) : rename cE (a.flip e)=b.flip (rename cE e) := by
    apply names_injective hE'
    rw [rename_names I hE hE']
    exact same_pad I hE hE' cE (⟨0,hI⟩ : Fin I) _ _ hf e
  have hsource (e : E) : rename cP (a.source e)=b.source (rename cE e) := by
    apply names_injective hP'
    rw [rename_names K hP hP']
    exact same_pad I hE hE' cE (⟨0,hK⟩ : Fin K) _ _ hs e
  exact ⟨⟨rename cP,rename cE,hflip,hsource,
    same_pad I hE hE' cE 0 _ _ hl,same_pad I hE hE' cE 0 _ _ hu,
    same_pad I hE hE' cE false _ _ hr,same_pad I hE hE' cE 0 _ _ ho⟩,rfl,rfl⟩

end TorsionFreeZeroDivisors.ComparisonCoding

namespace TorsionFreeZeroDivisors.SubdivisionIso
open scoped Classical
open ChainSubdivision PortSubdivision
variable {C V C' V' : Type*} (len : C → ℕ) (len' : C' → ℕ)
    (first last : C → V) (first' last' : C' → V')
    (eC : C ≃ C') (eV : V ≃ V') (hl : ∀ c,len c=len' (eC c))

def edge : Edge len ≃ Edge len' := Equiv.sigmaCongr eC (fun c => finCongr (hl c))
def interior : Interior len ≃ Interior len' := Equiv.sigmaCongr eC (fun c => finCongr (congrArg (fun n => n-1) (hl c)))
def vertex : Vertex len (V:=V) ≃ Vertex len' (V:=V') := Equiv.sumCongr eV (interior len len' eC hl)
def dart : Dart len ≃ Dart len' := Equiv.prodCongr (edge len len' eC hl) (Equiv.refl Bool)

variable (hf : ∀ c,eV (first c)=first' (eC c)) (ht : ∀ c,eV (last c)=last' (eC c))

include hf ht in
lemma point_eq (c : C) (k : Fin (len c+1)) :
    vertex len len' eC eV hl (point len first last c k)=
      point len' first' last' (eC c) ⟨k.val,by rw [←hl c]; exact k.isLt⟩ := by
  by_cases hz : k.val=0
  · simp [point,hz,vertex,hf]
  · by_cases ht' : k.val=len c
    · have hn : k.val=len' (eC c) := ht'.trans (hl c)
      simp only [point,dif_neg hz,dif_pos ht',dif_pos hn]
      exact congrArg Sum.inl (ht c)
    · have hn : k.val≠len' (eC c) := by rwa [←hl c]
      simp only [point,dif_neg hz,dif_neg ht',dif_neg hn]
      rfl

include hf ht in
lemma origin_eq (d : Dart len) :
    vertex len len' eC eV hl ((graph len first last).origin d)=
      (graph len' first' last').origin (dart len len' eC hl d) := by
  exact point_eq len len' first last first' last' eC eV hl hf ht d.1.1 _

omit eV in
lemma reverse_eq (d : Dart len) :
    dart len len' eC hl ((graph len first last).reverse d)=
      (graph len' first' last').reverse (dart len len' eC hl d) := rfl

end TorsionFreeZeroDivisors.SubdivisionIso

namespace TorsionFreeZeroDivisors.RankedSuppressionIso

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
def skeleton : PortGraph (Mark mark) {d : D // turn Γ.origin mark h2 d=d} where
  origin d := ⟨Γ.origin d.val,(turn_fixed_iff Γ.origin mark h2 _).mp d.property⟩
  reverse := (suppressed Γ mark h2).reverse
  reverse_reverse := (suppressed Γ mark h2).reverse_reverse
  reverse_ne := (suppressed Γ mark h2).reverse_ne

local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "R'" => Rep Γ' mark' h2'

lemma chosen_iff (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (d : B) : InvolutionOrientation.Chosen (S).reverse d ↔
    InvolutionOrientation.Chosen (S').reverse (f.dart d) := by
  unfold InvolutionOrientation.Chosen InvolutionOrientation.rank
  change (Fintype.equivFin B d).val < (Fintype.equivFin B ((S).reverse d)).val ↔
    (Fintype.equivFin B' (f.dart d)).val < (Fintype.equivFin B' ((S').reverse (f.dart d))).val
  rw [←f.reverse_eq,hrank,hrank]

def rep (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) : R ≃ R' :=
  f.dart.subtypeEquiv (chosen_iff Γ mark h2 Γ' mark' h2' f hrank)

lemma rep_length (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) (c : R) : repLength Γ mark h2 c=
    repLength Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := hlen c.val

lemma first_eq (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (c : R) : f.vertex (first Γ mark h2 c)=
    first Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := f.origin_eq c.val

lemma last_eq (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (c : R) : f.vertex (last Γ mark h2 c)=
    last Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := by
  change f.vertex ((S).origin ((S).reverse c.val))=(S').origin ((S').reverse (f.dart c.val))
  rw [f.origin_eq,f.reverse_eq]

/-- Exact canonical-rank suppression isomorphisms lift to actual subdivisions. -/
def subdivided (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) :
    Iso (ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2))
      (ChainSubdivision.graph (repLength Γ' mark' h2') (first Γ' mark' h2') (last Γ' mark' h2')) where
  vertex := SubdivisionIso.vertex _ _ (rep Γ mark h2 Γ' mark' h2' f hrank) f.vertex
    (rep_length Γ mark h2 Γ' mark' h2' f hrank hlen)
  dart := SubdivisionIso.dart _ _ (rep Γ mark h2 Γ' mark' h2' f hrank)
    (rep_length Γ mark h2 Γ' mark' h2' f hrank hlen)
  origin_eq := SubdivisionIso.origin_eq _ _ _ _ _ _ _ _ _
    (first_eq Γ mark h2 Γ' mark' h2' f hrank) (last_eq Γ mark h2 Γ' mark' h2' f hrank)
  reverse_eq := SubdivisionIso.reverse_eq _ _ _ _ _ _ _ _

variable (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
  (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
    Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)

def actual (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) :
    Iso (ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2)) Γ where
  vertex := vertexEquiv Γ mark h2 hcovered
  dart := dartEquiv Γ mark h2 hcovered
  origin_eq := origin_map Γ mark h2
  reverse_eq := dartMap_reverse Γ mark h2

include hcovered hcovered' in
/-- No vertex or dart names survive, but all actual graph incidence does. -/
def full (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) : Iso Γ Γ' :=
  ((actual Γ mark h2 hcovered).symm.trans (subdivided Γ mark h2 Γ' mark' h2' f hrank hlen)).trans
    (actual Γ' mark' h2' hcovered')

end

section
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "F'" => next Γ'.reverse (turn Γ'.origin mark' h2')
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'

lemma full_dartMap (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart (dartMap Γ mark h2 d)=
      dartMap Γ' mark' h2' ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).dart d) := by
  change (dartEquiv Γ' mark' h2' hcovered')
    ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).dart
      ((dartEquiv Γ mark h2 hcovered).symm ((dartEquiv Γ mark h2 hcovered) d))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma full_forward (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (c : R) (i : Fin (len c.val)) :
    (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart (F^[i.val] c.val.val)=
      F'^[i.val] (f.dart c.val).val :=
  full_dartMap Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen (⟨c,i⟩,false)

lemma full_iter (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (d : B) (i : ℕ) (hi : i<len d) :
    (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart (F^[i] d.val)=
      F'^[i] (f.dart d).val := by
  rcases InvolutionOrientation.chosen_or_reverse (S).reverse (S).reverse_reverse (S).reverse_ne d with hd|hd
  · exact full_forward Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen ⟨d,hd⟩ ⟨i,hi⟩
  · have hj : len d-i-1<len ((S).reverse d) := by
      change len d-i-1<len ((suppressed Γ mark h2).reverse d)
      rw [chainLength_reverse]
      omega
    have hj' : i<len' (f.dart d) := by rwa [←hlen d]
    apply Γ'.reverse_reverse.injective
    rw [←(full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).reverse_eq]
    rw [←ChainChunkTransport.reverse_iter Γ mark h2 d i hi,
      ←ChainChunkTransport.reverse_iter Γ' mark' h2' (f.dart d) i hj']
    have h := full_forward Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen
      ⟨(S).reverse d,hd⟩ ⟨len d-i-1,hj⟩
    have hrev : f.dart ((suppressed Γ mark h2).reverse d)=
        (suppressed Γ' mark' h2').reverse (f.dart d) := f.reverse_eq d
    simpa only [skeleton,hlen d,hrev] using h

lemma full_word (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (d : B) :
    (word Γ mark h2 d).map (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart =
      word Γ' mark' h2' (f.dart d) := by
  rw [word_eq_range,word_eq_range,List.map_map,←hlen d]
  apply List.map_congr_left
  intro i hi
  exact full_iter Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen d i (List.mem_range.mp hi)

end

open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'
variable (f : Iso (skeleton Γ mark h2) (skeleton Γ' mark' h2'))
    (hrank : ∀ d,(Fintype.equivFin {d : D' // turn Γ'.origin mark' h2' d=d} (f.dart d)).val=
      (Fintype.equivFin {d : D // turn Γ.origin mark h2 d=d} d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d))
local notation "F" => full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen

lemma full_seed (d : B) : (F).dart d.val=(f.dart d).val :=
  full_iter Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen d 0
    (chainLength_pos Γ mark h2 d)

lemma full_vertexMap (v : ChainSubdivision.Vertex (repLength Γ mark h2) (V:=Mark mark)) :
    (F).vertex (vertexMap Γ mark h2 v)=vertexMap Γ' mark' h2'
      ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).vertex v) := by
  change (vertexEquiv Γ' mark' h2' hcovered')
    ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).vertex
      ((vertexEquiv Γ mark h2 hcovered).symm ((vertexEquiv Γ mark h2 hcovered) v)))=_
  rw [Equiv.symm_apply_apply]
  rfl

variable (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v : Mark mark,side v.val=side' (f.vertex v).val)

include hside hs hs' in
lemma full_side (v : V) : side v=side' ((F).vertex v) := by
  obtain ⟨v,rfl⟩ := (vertexEquiv Γ mark h2 hcovered).surjective v
  change side (vertexMap Γ mark h2 v)=side' ((F).vertex (vertexMap Γ mark h2 v))
  rw [full_vertexMap]
  cases v with
  | inl v => exact hside v
  | inr v =>
    rcases v with ⟨c,i⟩
    change side (Γ.origin ((next Γ.reverse (turn Γ.origin mark h2))^[i.val+1] c.val.val))=
      side' (Γ'.origin ((next Γ'.reverse (turn Γ'.origin mark' h2'))^[i.val+1] (f.dart c.val).val))
    rw [ChainSide.iterate_side Γ mark h2 side hs,ChainSide.iterate_side Γ' mark' h2' side' hs']
    have he := congrArg (fun x : Mark mark' => side' x.val) (f.origin_eq c.val)
    exact (hside ((S).origin c.val)).trans he

variable {P P' : Type} (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
    (paths' : P' → List {d : D' // turn Γ'.origin mark' h2' d=d})
    (eP : P ≃ P') (hp : ∀ p,(paths p).map f.dart=paths' (eP p))

include hp in
lemma full_words (p : P) : ((paths p).flatMap (word Γ mark h2)).map (F).dart =
    (paths' (eP p)).flatMap (word Γ' mark' h2') := by
  rw [List.map_flatMap,←hp,List.flatMap_map]
  apply List.flatMap_congr
  intro d _
  exact full_word Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen d

variable (hne : ∀ p,paths p≠[]) (hne' : ∀ p,paths' p≠[])
    (root : Option P) (root' : Option P') (hroot : root.map eP=root')

include hp hroot in
lemma full_source : (StageRoot.source Γ mark h2 paths hne root).map (F).vertex=
    StageRoot.source Γ' mark' h2' paths' hne' root' := by
  rw [←hroot]
  cases root with
  | none => rfl
  | some p =>
    simp only [StageRoot.source,Option.map_some]
    apply congrArg some
    change (F).vertex (Γ.origin ((paths p).head (hne p)).val)=
      Γ'.origin ((paths' (eP p)).head (hne' _)).val
    rw [(F).origin_eq,full_seed]
    have hh := congrArg List.head? (hp p)
    rw [List.head?_map,List.head?_eq_some_head (hne p),
      List.head?_eq_some_head (hne' (eP p))] at hh
    exact congrArg (fun d => Γ'.origin d.val) (Option.some.inj hh)

end TorsionFreeZeroDivisors.RankedSuppressionIso

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternTotalCoding
open scoped Classical
open PatternCoding

abbrev Code (R K T I H : ℕ) := SizedCode R K T 0 H ×
  (Fin R → Bool) × Fin (I+1) × ComparisonCoding.Code K I H

lemma card_code_bound (R K T I H : ℕ) : Fintype.card (Code R K T I H) ≤
    coefficient R K T I*(H+1)^(R+3*I) := by
  have h1 := card_sizedCode R K T 0 H
  have h2 := ComparisonCoding.card_code_bound K I H
  simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.mul_one] at h1
  have h := Nat.mul_le_mul (Nat.mul_le_mul_right (2^R*(I+1)) h1) h2
  have he : Fintype.card (Code R K T I H)=Fintype.card (SizedCode R K T 0 H)*(2^R*((I+1)*Fintype.card (ComparisonCoding.Code K I H))) := by
    simp only [Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [he]
  simp only [coefficient,pow_add]
  convert h using 1 <;> ring

variable {D V P E D' V' P' E' : Type*}
    [Fintype D] [Fintype V] [Fintype P] [Fintype E]
    [Fintype D'] [Fintype V'] [Fintype P'] [Fintype E']
    (R K T I H : ℕ) (hR : 0<R) (hK : 0<K) (hI : 0<I)
    (hD : Fintype.card D≤R) (hV : Fintype.card V≤R)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

def encode (a : Data D V P (Fin 0) T H) (side : V → Bool)
    (c : ComparisonCoding.Data P E H) : Code R K T I H :=
  (encodeData R K T 0 H hR hD hV hP (by simp) a,
   pad R hV false side,⟨Fintype.card E,by omega⟩,ComparisonCoding.encode K I H hK hI hP hE c)

variable (hD' : Fintype.card D'≤R) (hV' : Fintype.card V'≤R)
    (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

/-- Complete simultaneous code equivalence for graph, every marked vertex side,
path words, root and the full affine interval geometry. Padding loses no data. -/
theorem complete (a : Data D V P (Fin 0) T H) (side : V → Bool)
    (c : ComparisonCoding.Data P E H)
    (a' : Data D' V' P' (Fin 0) T H) (side' : V' → Bool)
    (c' : ComparisonCoding.Data P' E' H)
    (he : encode R K T I H hR hK hI hD hV hP hE a side c=
      encode R K T I H hR hK hI hD' hV' hP' hE' a' side' c') :
    ∃ f : PatternCoding.Isomorphism a a', ∃ g : ComparisonCoding.Isomorphism H c c',
      f.path=g.path ∧ (∀ d,(Fintype.equivFin D' (f.dart d)).val=(Fintype.equivFin D d).val) ∧
      ∀ v,side v=side' (f.vertex v) := by
  simp only [encode,encodeData,Prod.mk.injEq] at he
  obtain ⟨⟨cd,cv,cp,_,ha⟩,hs,ce,hc⟩ := he
  have cD : Fintype.card D=Fintype.card D' := congrArg Fin.val cd
  have cV : Fintype.card V=Fintype.card V' := congrArg Fin.val cv
  have cP : Fintype.card P=Fintype.card P' := congrArg Fin.val cp
  have cE : Fintype.card E=Fintype.card E' := congrArg Fin.val ce
  obtain ⟨f,fd,fp,fv⟩ := same_code_canonical_isomorphism R K T 0 H hR hD hV hP (by simp)
    hD' hV' hP' (by simp) a a' cD cV cP rfl ha
  obtain ⟨g,gp,_⟩ := ComparisonCoding.encode_complete K I H hK hI hP hE hP' hE' c c' cP cE hc
  refine ⟨f,g,fp.trans gp.symm,?_,?_⟩
  · intro d
    rw [fd]
    exact rename_rank cD d
  · intro v
    rw [fv]
    exact same_pad R hV hV' cV false side side' hs v

end TorsionFreeZeroDivisors.PatternTotalCoding

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks RankedSuppressionIso

attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {R K T I H : ℕ} (a : Data R K T I H)

abbrev Seeds := {d : a.D // turn a.graph.origin a.mark a.degree_two d=d}
abbrev Marks := Mark a.mark

def graphData : PatternCoding.Data a.Seeds a.Marks a.P (Fin 0) T H where
  reverse := (skeleton a.graph a.mark a.degree_two).reverse
  origin := (skeleton a.graph a.mark a.degree_two).origin
  side d := a.side (a.graph.origin d.val)
  length d := ⟨chainLength a.graph a.mark a.degree_two d,by have := a.chain_length_bound d; omega⟩
  paths := a.paths
  path_bound := a.traversal_bound
  root := a.root.map (fun p => (p,true))
  comparisons := Fin.elim0

def geometryData : ComparisonCoding.Data a.P a.E H where
  flip := a.comparisons.flip
  source := a.comparisons.source
  lower := a.lower
  upper := a.upper
  reverse := a.comparisons.reverse
  offset := a.offset

def encode (hR : 0<R) (hK : 0<K) (hI : 0<I) : PatternTotalCoding.Code R K T I H :=
  PatternTotalCoding.encode R K T I H hR hK hI a.dart_bound a.vertex_bound
    a.path_bound a.comparison_bound a.graphData (fun v => a.side v.val) a.geometryData

end Data
end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.PatternFiniteUnion
open scoped Classical

/-- Quotient-free finite union over a possibly large class of finite graphs.
Representatives are chosen only for used codes, and encode equality must preserve
the literal sample event. -/
theorem bound {P : Type*} {C Ω : Type*} [Fintype C]
    (sample : Finset Ω) (hs : sample.Nonempty) (code : P → C) (good : P → Prop)
    (event : P → Ω → Prop) (B : ℝ) (hB : 0≤B)
    (hinv : ∀ p q, code p=code q → ∀ ω,event p ω → event q ω)
    (hp : ∀ p,good p → ((sample.filter (event p)).card:ℝ)/sample.card≤B) :
    ((sample.filter (fun ω => ∃ p,good p ∧ event p ω)).card:ℝ)/sample.card≤
      (Fintype.card C:ℝ)*B := by
  let Used := {c : C // ∃ p,good p ∧ code p=c}
  let representative (c : Used) : P := Classical.choose c.property
  have hr (c : Used) : good (representative c) ∧ code (representative c)=c.val :=
    Classical.choose_spec c.property
  have hc : sample.filter (fun ω => ∃ p,good p ∧ event p ω)⊆
      sample.filter (fun ω => ∃ c : Used,event (representative c) ω) := by
    intro ω hω
    obtain ⟨hω,p,hp,he⟩ := Finset.mem_filter.mp hω
    refine Finset.mem_filter.mpr ⟨hω,?_,?_⟩
    · exact ⟨code p,p,hp,rfl⟩
    · exact hinv p (representative ⟨code p,p,hp,rfl⟩) (hr (⟨code p,p,hp,rfl⟩ : Used)).2.symm ω he
  calc
    _ ≤ ((sample.filter (fun ω => ∃ c : Used,event (representative c) ω)).card:ℝ)/sample.card :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hc)) (Nat.cast_nonneg _)
    _ ≤ (Fintype.card Used:ℝ)*B :=
      StageFusion.pattern_union sample hs _ B (fun c => hp _ (hr c).1)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _)) hB

end TorsionFreeZeroDivisors.PatternFiniteUnion

namespace TorsionFreeZeroDivisors.BoundedPattern.Data

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks RankedSuppressionIso
variable {R K T I H : ℕ} (a b : Data R K T I H)

/-- Equal finite codes transport every fixed matching event, including both
pinned source sides. The code does not contain any graph labels. -/
theorem event_of_encode_eq (hR : 0<R) (hK : 0<K) (hI : 0<I)
    (he : a.encode hR hK hI=b.encode hR hK hI)
    (rep : ℕ) (x : Types.VertexA rep) (y : Types.VertexB rep) (r : ActualPatternEvent.Match rep)
    (hb : b.event rep x y r) : a.event rep x y r := by
  obtain ⟨f,g,hpg,hrank,hside⟩ := PatternTotalCoding.complete R K T I H hR hK hI
    a.dart_bound a.vertex_bound a.path_bound a.comparison_bound
    b.dart_bound b.vertex_bound b.path_bound b.comparison_bound
    a.graphData (fun v => a.side v.val) a.geometryData
    b.graphData (fun v => b.side v.val) b.geometryData he
  let f₀ : PortSubdivision.Iso (skeleton a.graph a.mark a.degree_two)
      (skeleton b.graph b.mark b.degree_two) :=
    ⟨f.vertex,f.dart,f.origin_eq,f.reverse_eq⟩
  have hlen (d : a.Seeds) : chainLength a.graph a.mark a.degree_two d=
      chainLength b.graph b.mark b.degree_two (f₀.dart d) := congrArg Fin.val (f.length_eq d)
  let F := full a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
  have words (p : a.P) : ((a.paths p).flatMap (word a.graph a.mark a.degree_two)).map F.dart=
      (b.paths (f.path p)).flatMap (word b.graph b.mark b.degree_two) :=
    full_words a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered
      f₀ hrank hlen a.paths b.paths f.path f.paths_eq p
  have hroot : a.root.map f.path=b.root := by
    have hh := congrArg (Option.map Prod.fst) f.root_eq
    simpa [graphData,Option.map_map,Function.comp_def] using hh
  have sides (v : a.V) : a.side v=b.side (F.vertex v) :=
    full_side a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
      a.side b.side a.side_edge b.side_edge hside v
  have roots : (StageRoot.source a.graph a.mark a.degree_two a.paths a.nonempty a.root).map F.vertex=
      StageRoot.source b.graph b.mark b.degree_two b.paths b.nonempty b.root :=
    full_source a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
      a.paths b.paths f.path f.paths_eq a.nonempty b.nonempty a.root b.root hroot
  let geometry : ComparisonGeometry.Iso a.comparisons b.comparisons := {
    path := f.path
    comparison := g.comparison
    length_eq := OriginalPatternIso.length_eq a.graph a.mark a.degree_two b.graph b.mark b.degree_two
      a.paths b.paths F f.path words
    flip_eq := g.flip_eq
    source_eq := by intro e; rw [hpg]; exact g.source_eq e
    lo_eq := by
      intro e
      rw [a.lower_eq,b.lower_eq]
      exact_mod_cast congrArg Fin.val (g.lower_eq e)
    hi_eq := by
      intro e
      rw [a.upper_eq,b.upper_eq]
      exact_mod_cast congrArg Fin.val (g.upper_eq e)
    reverse_eq := g.reverse_eq
    offset_eq := by
      intro e
      rw [a.offset_eq,b.offset_eq]
      have ho := congrArg Fin.val (g.offset_eq e)
      exact congrArg (fun n : ℕ => (n:ℤ)-2*H) ho }
  exact OriginalPatternIso.realized a.graph a.mark a.degree_two b.graph b.mark b.degree_two
    a.paths a.nonempty b.paths b.nonempty F f.path words a.side b.side a.side_edge b.side_edge
    sides a.root b.root roots a.comparisons b.comparisons geometry rfl rep x y r hb

end

open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
open GridAsymptotics GirthAsymptotics TypedGraphs
variable {R K T I H : ℕ} (a : Data R K T I H)

lemma probability_bound (B Q M J rep : ℕ) (hM : 0<M) (hready : PatternUniform.Ready B M Q J rep)
    (hg : a.Good B Q M J rep) (x : Types.VertexA rep) (y : Types.VertexB rep) :
    (((samples rep).filter (a.event rep x y)).card:ℝ)/(samples rep).card≤
      Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  exact OriginalPattern.probability_bound a.graph a.mark a.degree_two a.side a.side_edge a.paths a.nonempty
    a.root rep x y a.comparisons (fun e => (a.lower e).val) (fun e => (a.upper e).val)
    (by simpa only [Int.cast_natCast] using a.lower_eq)
    (by simpa only [Int.cast_natCast] using a.upper_eq)
    B Q M J hM hready hg.multiplicity_le hg.multiplicity_pos hg.path_chain hg.cyclic_chain
    hg.reduced hg.chains_le hg.cut_comparisons_le hg.length_le hg.length_ge hg.unpaired_le

end TorsionFreeZeroDivisors.BoundedPattern.Data

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open ActualPatternEvent GirthAsymptotics TypedGraphs

/-- Uniform first-moment union over every actual-carrier pattern, not over a
postulated finite list of realizations. -/
theorem probability_union_dev (R K T I H B Q M J rep : ℕ)
    (hR : 0<R) (hK : 0<K) (hI : 0<I) (hM : 0<M)
    (hs : (samples rep).Nonempty) (hready : PatternUniform.Ready B M Q J rep)
    (x : Types.VertexA rep) (y : Types.VertexB rep) :
    (((samples rep).filter (fun r => ∃ a : Data R K T I H,a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ)/
      (samples rep).card≤
      (PatternTotalCoding.coefficient R K T I:ℝ)*(H+1:ℕ)^(R+3*I)*
        Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  have he := PatternFiniteUnion.bound (samples rep) hs (fun a : Data R K T I H => a.encode hR hK hI)
    (fun a => a.Good B Q M J rep) (fun a => a.event rep x y) _ (Real.exp_pos _).le
    (fun a b hab r ha => b.event_of_encode_eq a hR hK hI hab.symm rep x y r ha)
    (fun a ha => a.probability_bound B Q M J rep hM hready ha x y)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast PatternTotalCoding.card_code_bound R K T I H

end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.ActualComplexity
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression
open ChainSuppression SuppressedMoore ChainPaths ChainIsomorphism ChainChunkTransport
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P] (Γ : PortGraph V D)

variable (paths : P → List D) (hp : ∀ p,paths p≠[])

end TorsionFreeZeroDivisors.ActualComplexity

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.FiniteClusters
open scoped Classical BigOperators
variable {V : Type} [Fintype V] (G : SimpleGraph V)
local instance : Fintype G.ConnectedComponent := Fintype.ofFinite _

end TorsionFreeZeroDivisors.FiniteClusters

namespace TorsionFreeZeroDivisors.PairingClusters
open scoped Classical BigOperators
variable {O T : Type} [Fintype O] [Fintype T]
    (f : O → T) (α : O → O) (hα : Function.Involutive α) (keep : T → Prop)
end TorsionFreeZeroDivisors.PairingClusters

/-! Arithmetic localization of finite-cluster mass and comparison bounds. -/
namespace TorsionFreeZeroDivisors.PlanarLocalization
open scoped Classical BigOperators

end TorsionFreeZeroDivisors.PlanarLocalization

namespace TorsionFreeZeroDivisors.ClusterLocalization
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)

end TorsionFreeZeroDivisors.ClusterLocalization

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords
namespace TorsionFreeZeroDivisors.SingleException
open scoped Classical BigOperators
variable {T : Type} [Fintype T] (root : Option T) (f : T → ℕ) (L : ℕ)
end TorsionFreeZeroDivisors.SingleException
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (U : ℕ) (hU : 3≤U)
    (hL : 1≤L (size rep)) (hcap : 6≤U*L (size rep))
    (hd : GraphSample.Diameters rep r) (hr : r∈samples rep)
    (hordinary : ∃t,s.root≠some t)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

/-! Finite rotation systems. The Euler inequality here
is explicitly an input from a planar realization; no PL realization or planar
separator theorem is asserted by this file. The face cycles and bad-gap count,
however, are computed from the actual boundary and pairing permutations. -/
namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
instance : Fintype (Cycle f) := Fintype.ofFinite _

end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.PlanarRotation
open scoped Classical BigOperators
open PermutationCycles

variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.PlanarRotation
namespace TorsionFreeZeroDivisors.PlanarRuns
open scoped Classical BigOperators
open PlanarRotation
variable {O : Type}

namespace CutSystem
variable {σ : Equiv.Perm O} (S : CutSystem σ)

namespace Paired
variable {S}
variable {α : Equiv.Perm O} (P : S.Paired α)
include P

end Paired
namespace PairOrbit
variable {A : Type} (r : A→A) (hr : Function.Involutive r)
variable [Fintype A]
end PairOrbit

namespace Paired
variable {S} {α : Equiv.Perm O} (P : S.Paired α)
end Paired

end CutSystem
end TorsionFreeZeroDivisors.PlanarRuns

namespace TorsionFreeZeroDivisors.PlanarIntervals
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks PlanarRuns PlanarRuns.CutSystem
variable {T : Type} {len : T→ℕ} {σ α : Equiv.Perm (Position len)}
    (S : CutSystem σ) (P : S.Paired α)
    (hstep : ∀ x,x∉S.cut → (σ x).1=x.1 ∧ (σ x).2.val=x.2.val+1)

include hstep
end TorsionFreeZeroDivisors.PlanarIntervals
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T → ℕ} (C : Comparisons (E:=E) len)
    (hle : ∀ t,len t ≤ more t)

variable (hupper : ∀ e,C.hi e≤len (C.source e))

variable [Fintype T]
end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.WordPositions

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A)

variable (cap : ℕ) (hc : 0<cap)
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} [Fintype T] (len : T → ℕ)
variable {A : Type} (w v : T → List A)
variable {E : Type} (C : Comparisons (E:=E) (fun t=>(w t).length))
end TorsionFreeZeroDivisors.WordPositions

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r) {E : Type} [Fintype E] (lo hi : E → ℕ) (hle : ∀ e,lo e≤hi e)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

namespace TorsionFreeZeroDivisors.BoundaryRotation

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T : Type} (len : T → ℕ)
variable [Fintype T]
end

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (len : T → ℕ) (root : Option T) (label : Position len → A) (bar : A → A) (α : Equiv.Perm (Position len)) (hr : Function.Involutive α) (hcomp : ∀ x,label (α x)=bar (label x))
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A) (R : A → A → Prop)
end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRotation WeightedMoore ActualPatternEvent GirthAsymptotics
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.PermutationTransport
variable {A B : Type} (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.BalancedRotation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (w : T → List A) (cap : ℕ) (hc : 0<cap)
end TorsionFreeZeroDivisors.BalancedRotation

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
namespace FullPairing
variable {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end FullPairing
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.PermutationTransport
open PermutationCycles
variable {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent PermutationCycles PlanarRotation
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

/-! Recursive separation. This is the actual deletion-set
construction and sharp charging estimate. The one-step Lipton–Tarjan theorem
is kept as an explicit dependency, not asserted from an unspecified planar
predicate.  No claim of a completed planar realization is made here. -/
namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] (R : V → V → Prop)

namespace Split
variable {R} {S : Finset V} (P : Split R S)
end Split

namespace Split
variable {R} {S : Finset V} (P : Split R S) (D : Finset V → Finset V)
end Split

end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarParameters
open scoped Classical
open RecursiveSeparator
variable (ε : ℝ) (D : ℕ)
end TorsionFreeZeroDivisors.PlanarParameters

namespace TorsionFreeZeroDivisors.LocalizationCounts
open scoped Classical BigOperators
open ComparedBlocks BlockAlignment
variable {T E : Type} [Fintype T] {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop) (old : T → ℕ)

end TorsionFreeZeroDivisors.LocalizationCounts

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y)
local instance : Fintype s.P := s.fP
local instance : Fintype s.E := s.fE

end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (hL : 2≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

namespace TorsionFreeZeroDivisors.PermutationCycles
variable {O B : Type} [Fintype O] (f : Equiv.Perm O)
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.InsertedRotation
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (p : O)

variable [Fintype O]

end TorsionFreeZeroDivisors.InsertedRotation

namespace TorsionFreeZeroDivisors.SwapCycles

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)

variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (p q : O)
end TorsionFreeZeroDivisors.SwapCycles

namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.DeleteCycle

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
variable {O B : Type} (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
end
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)

variable (hs : σ p≠p)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler

/-! Actual finite noncrossing word matchings, the cancellation part of the
cone-picture construction. An ear is inserted at two adjacent positions.
This file asserts no sphere realization or asphericity theorem. -/
namespace TorsionFreeZeroDivisors.WordPairing

section
variable {A : Type*} {n : ℕ}

namespace Ear
variable (k : ℕ)

variable {inv : A → A} {label : Fin n → A}
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
end Data

namespace Ear
variable (k : ℕ) (hk : k≤n) (a : A)
end Ear

namespace ListInsert
variable (u v : List A) (a b : A)
end ListInsert

end
variable {A : Type*}
namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.Ear
open PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
variable (k : ℕ) (hk : k≤n) (hn : 0<n)

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Ear
variable (k : ℕ) (hk : k≤n)
end Ear

namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.EraseEar
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A} (k : ℕ) (hk : k≤n)
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.MapEuler
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
open MapEuler PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin n→A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.DeleteCycle
open scoped Classical
variable {O : Type} (σ : Equiv.Perm O) (p : O)
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.IsolatedDeletion
open scoped Classical
open MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
variable [Fintype O]
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.BoundarySurgery
open scoped Classical
variable {O V : Type} [Fintype O] (σ : Equiv.Perm O) (before after : O→V)
variable (p q : O) (hpq : p≠q)
end TorsionFreeZeroDivisors.BoundarySurgery

namespace TorsionFreeZeroDivisors.VertexSplit
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O) (l : List (O×O)) (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α) (he : ∀e∈l,α e.1=e.2)
local notation "σ'" => Equiv.swap p q*σ
local notation "L'" => (α p,α q)::l
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapConjugation
open scoped Classical
open MapEuler PermutationCycles
variable {A B : Type} (e : A ≃ B) (σ α : Equiv.Perm A)
local notation "σ'" => e.permCongr σ
local notation "α'" => e.permCongr α
variable [Fintype A] [Fintype B]
end TorsionFreeZeroDivisors.MapConjugation

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.MatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (hf : ∀x,α x≠x) (p q : O) (hpq : p≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.MatchingSurgery
namespace TorsionFreeZeroDivisors.Smoothing
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (hf : ∀x,α x≠x)
  (p q : O) (hpq : p≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.Smoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
open PermutationCycles
variable {O V : Type} (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)

variable [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀x,α x≠x)

variable (before after : O→V)
end TorsionFreeZeroDivisors.Tightening

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.PartialMatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.PartialMatchingSurgery
namespace TorsionFreeZeroDivisors.PartialSmoothing
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.PartialSmoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
variable {O : Type} [Fintype O] (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
  (α : Equiv.Perm O) (hi : Function.Involutive α) (hfp : α p≠p) (hfq : α q≠q)
end TorsionFreeZeroDivisors.Tightening
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V) [Fintype O]
namespace Data
variable {Γ label inv x y}

variable {O' : Type} [Fintype O']

variable (p q : O) (hpq : p≠q)
end Data
end TorsionFreeZeroDivisors.FinitePicture

namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
end TorsionFreeZeroDivisors.PermutationCycles
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open MapEuler PermutationCycles
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V}
variable (hxy : x≠y)
end TorsionFreeZeroDivisors.FinitePicture.Data

/-! Exact finite permutation cycles, including singleton cycles, as nonempty
lists with their literal successor. This is the coordinate bridge from marked
picture surgery to boundary words; it asserts no geometric realization. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {A : Type*}
open FreeGroup

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I→List (A×Bool))

end TorsionFreeZeroDivisors.AlgebraicPictures

namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

namespace Path
variable {Γ} {a b c : V}
@[simp] lemma eval_nil {G : Type*} [_root_.Group G] (label : D→G) (v : V) :
    (Path.nil (Γ:=Γ) v).eval label=1 := rfl
@[simp] lemma eval_cons {G : Type*} [_root_.Group G] (label : D→G) (d : D)
    (p : Path Γ (Γ.origin (Γ.reverse d)) b) :
    (Path.cons d p).eval label=label d*p.eval label := rfl
@[simp] lemma eval_append {G : Type*} [_root_.Group G] (label : D→G)
    (p : Path Γ a b) (q : Path Γ b c) :
    (p.append q).eval label=p.eval label*q.eval label := by
  induction p with
  | nil v => simp [append]
  | cons d p ih => simp only [append,eval_cons,ih,mul_assoc]
@[simp] lemma eval_single {G : Type*} [_root_.Group G] (label : D→G) (d : D) :
    (single (Γ:=Γ) d).eval label=label d := by simp [single]
@[simp] lemma eval_cast {G : Type*} [_root_.Group G] (label : D→G)
    {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) :
    (p.cast ha hb).eval label=p.eval label := by
  subst a'; subst b'; rfl

end Path
end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b c : V}
variable {A : Type*} (label : D→A×Bool)

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {D A : Type*} (label : D→A)

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.MarkerInsertion
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O) (p : O)
variable [Fintype O]

end TorsionFreeZeroDivisors.MarkerInsertion
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V)
  (σ α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀i,α i≠i)
  (edge : O→D) (p : O)
  (hc : ∀i,label (edge (α i))=inv (label (edge i)))
  (hj : ∀i,σ i≠p → Γ.origin (Γ.reverse (edge i))=Γ.origin (edge (σ i)))
  (hp : Γ.origin (edge p)=x)
  (he : ∀i,σ i=p → Γ.origin (Γ.reverse (edge i))=y)
  (hz : MapEuler.GenusZero σ α)

end TorsionFreeZeroDivisors.FinitePicture

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b : V}

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A)
variable {x y : V} (p : Path Γ x y) (hxy : x≠y) (ws : List (List D))

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
variable {A I : Type*} (rel : I→List (A×Bool))
open FreeGroup
end TorsionFreeZeroDivisors.AlgebraicPictures
namespace TorsionFreeZeroDivisors.InitialPicture
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A I : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
variable {x y : V} (p : Path Γ x y)

end TorsionFreeZeroDivisors.InitialPicture

namespace TorsionFreeZeroDivisors.GraphPresentation

section
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

variable {S : Type*} (letters : D→FreeGroup S) (R : Routes Γ)

instance [Finite S] [Finite D] : _root_.Group.IsFinitelyPresented (Group Γ letters R) := by
  have : Finite (relations Γ letters R) := Set.finite_range (relator Γ letters R) |>.to_subtype
  infer_instance

end

open scoped Classical
open PortSubdivision
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d)) (R : Routes Γ)

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
variable {V D A B O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V} (f : A→B) (label' : D→B) (inv' : B→B) (hl : ∀d,label' d=f (label d)) (hf : ∀t,f (inv t)=inv' (f t))

end TorsionFreeZeroDivisors.FinitePicture.Data
namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)
namespace Path
variable {Γ}
end Path

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.ConcreteGroup

section
open scoped Classical BigOperators
open PortSubdivision TypedGraphs ConditionedMatchings SampleGraph
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
instance : Group.IsFinitelyPresented (G rep r) := inferInstance
end

open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)

end TorsionFreeZeroDivisors.ConcreteGroup

end

end OAI
end

section
namespace OAI



section
namespace TorsionFreeZeroDivisors.CellNorm
open scoped Classical BigOperators
noncomputable section
variable {H G I : Type} [CommGroup H] [_root_.Group G] [Fintype H]
  (φ : H→*G) (hφ : Function.Injective φ)
@[instance_reducible] def moduleAction : MulAction H (G×I) where
  smul h p := (φ h*p.1,p.2)
  one_smul p := by change (φ 1*p.1,p.2)=p; simp
  mul_smul h k p := by change (φ (h*k)*p.1,p.2)=(φ h*(φ k*p.1),p.2); rw [map_mul,mul_assoc]
end
end TorsionFreeZeroDivisors.CellNorm

end



end OAI
end

open scoped Classical in
open OAI.TorsionFreeZeroDivisors OAI.TorsionFreeZeroDivisors.BoundedPattern ActualPatternEvent GirthAsymptotics TypedGraphs in
theorem solution (R K T I H B Q M J rep : ℕ)
    (hR : 0<R) (hK : 0<K) (hI : 0<I) (hM : 0<M)
    (hs : (samples rep).Nonempty) (hready : PatternUniform.Ready B M Q J rep)
    (x : Types.VertexA rep) (y : Types.VertexB rep) :
    (((samples rep).filter (fun r => ∃ a : Data R K T I H,a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ)/
      (samples rep).card≤
      (PatternTotalCoding.coefficient R K T I:ℝ)*(H+1:ℕ)^(R+3*I)*
        Real.exp (-(L (size rep):ℝ)/(4800*M)) :=
  OAI.TorsionFreeZeroDivisors.BoundedPattern.probability_union_dev R K T I H B Q M J rep hR hK hI hM hs hready x y
