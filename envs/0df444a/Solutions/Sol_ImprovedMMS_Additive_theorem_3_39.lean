-- Prove2me | solution 1 for ImprovedMMS.Additive.theorem_3_39
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T04:43:00.782353+00:00
-- url     : https://prove2.me/submissions/649080e7-a637-41e1-bf3a-fa60b5c5c0cc

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance

open LittleCharity.MMS

-- ===== part A =====

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

namespace MMS34

variable {m : ℕ}

/-- A single additive, non-negative valuation. -/
def Add1 (w : Finset (Fin m) → ℝ) : Prop := (∀ S, w S = ∑ g ∈ S, w {g}) ∧ ∀ S, 0 ≤ w S

lemma add1_of {n : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hv : IsAdditive v) (i : Fin n) :
    Add1 (v i) := ⟨hv.1 i, hv.2 i⟩

namespace Add1
variable {w : Finset (Fin m) → ℝ}

lemma sing_nonneg (hw : Add1 w) (g : Fin m) : 0 ≤ w {g} := hw.2 _

lemma mono (hw : Add1 w) {S T : Finset (Fin m)} (h : S ⊆ T) : w S ≤ w T := by
  rw [hw.1 S, hw.1 T]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun g _ _ => hw.sing_nonneg g)

lemma union (hw : Add1 w) {S T : Finset (Fin m)} (h : Disjoint S T) :
    w (S ∪ T) = w S + w T := by
  rw [hw.1, hw.1 S, hw.1 T, Finset.sum_union h]

lemma empty (hw : Add1 w) : w ∅ = 0 := by rw [hw.1]; simp

lemma pair (hw : Add1 w) {g h : Fin m} (hne : g ≠ h) : w {g, h} = w {g} + w {h} := by
  rw [hw.1, Finset.sum_pair hne]

lemma erase (hw : Add1 w) {S : Finset (Fin m)} {g : Fin m} (hg : g ∈ S) :
    w (S.erase g) = w S - w {g} := by
  rw [hw.1, hw.1 S, Finset.sum_erase_eq_sub hg]

lemma insert (hw : Add1 w) {S : Finset (Fin m)} {g : Fin m} (hg : g ∉ S) :
    w (insert g S) = w {g} + w S := by
  rw [hw.1, hw.1 S, Finset.sum_insert hg]

lemma sdiff (hw : Add1 w) {S T : Finset (Fin m)} (h : S ⊆ T) : w (T \ S) = w T - w S := by
  rw [hw.1, hw.1 S, hw.1 T, Finset.sum_sdiff_eq_sub h]

end Add1

/-- `mms` with the standard decidability instance. -/
lemma mms_eq (w : Finset (Fin m) → ℝ) (k : ℕ) (S : Finset (Fin m)) :
    mms w k S = ⨆ f : Fin m → Fin k, ⨅ j : Fin k, w (S.filter (fun g => f g = j)) := by
  unfold mms
  congr 1


lemma mms_attained (w : Finset (Fin m) → ℝ) {k : ℕ} (hk : 0 < k) (S : Finset (Fin m)) :
    ∃ f : Fin m → Fin k, ∀ j, mms w k S ≤ w (S.filter (fun g => f g = j)) := by
  have : Nonempty (Fin m → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite
    (f := fun f : Fin m → Fin k => ⨅ j : Fin k, w (S.filter (fun g => f g = j)))
  refine ⟨f, fun j => ?_⟩
  rw [mms_eq, ← hf]
  exact ciInf_le (Finite.bddBelow_range _) j

lemma le_mms_of_labels (w : Finset (Fin m) → ℝ) {k : ℕ} (hk : 0 < k) (S : Finset (Fin m))
    (f : Fin m → Fin k) (c : ℝ) (h : ∀ j, c ≤ w (S.filter (fun g => f g = j))) :
    c ≤ mms w k S := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [mms_eq]
  exact le_ciSup_of_le (Finite.bddAbove_range _) f (le_ciInf h)

/-- A disjoint family of `k` bundles inside `S`, each worth at least `c`, witnesses
`c ≤ MMS^k(S)`. -/
lemma le_mms_of_family {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (hk : 0 < k)
    (S : Finset (Fin m)) (T : Fin k → Finset (Fin m))
    (hdisj : ∀ a b, a ≠ b → Disjoint (T a) (T b)) (hsub : ∀ a, T a ⊆ S) (c : ℝ)
    (hc : ∀ a, c ≤ w (T a)) : c ≤ mms w k S := by
  classical
  let f : Fin m → Fin k := fun g => if h : ∃ j, g ∈ T j then Classical.choose h else ⟨0, hk⟩
  refine le_mms_of_labels w hk S f c (fun j => (hc j).trans (hw.mono ?_))
  intro g hg
  refine Finset.mem_filter.mpr ⟨hsub j hg, ?_⟩
  have hex : ∃ j, g ∈ T j := ⟨j, hg⟩
  simp only [f, dif_pos hex]
  by_contra hne
  exact Finset.disjoint_left.mp (hdisj _ _ hne) (Classical.choose_spec hex) hg

lemma mms_nonneg {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (hk : 0 < k)
    (S : Finset (Fin m)) : 0 ≤ mms w k S :=
  le_mms_of_labels w hk S (fun _ => ⟨0, hk⟩) 0 (fun _ => hw.2 _)

/-- The parts of a labelling sum to the whole. -/
lemma sum_parts {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (S : Finset (Fin m))
    (f : Fin m → Fin k) : ∑ j, w (S.filter (fun g => f g = j)) = w S := by
  rw [hw.1 S, ← Finset.sum_fiberwise S f (fun g => w {g})]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hw.1]

/-- Lemma 2.3: `k · MMS^k(S) ≤ w(S)`. -/
lemma mms_mul_le {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (hk : 0 < k)
    (S : Finset (Fin m)) : (k : ℝ) * mms w k S ≤ w S := by
  obtain ⟨f, hf⟩ := mms_attained w hk S
  calc (k : ℝ) * mms w k S = ∑ _j : Fin k, mms w k S := by simp
    _ ≤ ∑ j, w (S.filter (fun g => f g = j)) := Finset.sum_le_sum (fun j _ => hf j)
    _ = w S := sum_parts hw S f

end MMS34

-- ===== part A2 =====

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

namespace MMS34

variable {m : ℕ}

/-! ### Positions of goods in a set `M`, ordered as in `Fin m` -/

noncomputable def ePos (M : Finset (Fin m)) (d : Fin m) (p : ℕ) : Fin m :=
  if h : p < M.card then M.orderEmbOfFin rfl ⟨p, h⟩ else d

section ePos
variable {M : Finset (Fin m)} {d : Fin m} {p q : ℕ}

lemma ePos_of_lt (h : p < M.card) : ePos M d p = M.orderEmbOfFin rfl ⟨p, h⟩ := dif_pos h

lemma ePos_mem (h : p < M.card) : ePos M d p ∈ M := by
  rw [ePos_of_lt h]; exact Finset.orderEmbOfFin_mem _ _ _

lemma ePos_lt_iff (hp : p < M.card) (hq : q < M.card) : ePos M d p < ePos M d q ↔ p < q := by
  rw [ePos_of_lt hp, ePos_of_lt hq, OrderEmbedding.lt_iff_lt]; rfl

lemma ePos_le_iff (hp : p < M.card) (hq : q < M.card) : ePos M d p ≤ ePos M d q ↔ p ≤ q := by
  rw [ePos_of_lt hp, ePos_of_lt hq, OrderEmbedding.le_iff_le]; rfl

lemma ePos_inj (hp : p < M.card) (hq : q < M.card) : ePos M d p = ePos M d q ↔ p = q := by
  constructor
  · intro h
    exact le_antisymm ((ePos_le_iff hp hq).mp h.le) ((ePos_le_iff hq hp).mp h.ge)
  · rintro rfl; rfl

lemma ePos_surj {g : Fin m} (hg : g ∈ M) : ∃ p < M.card, ePos M d p = g := by
  have : g ∈ Set.range (M.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hg
  obtain ⟨⟨p, hp⟩, hpe⟩ := this
  exact ⟨p, hp, by rw [ePos_of_lt hp]; exact hpe⟩

end ePos

/-- An ordered valuation on `M`: goods earlier in the order of `Fin m` are worth more. -/
def Ord (w : Finset (Fin m) → ℝ) (M : Finset (Fin m)) : Prop :=
  ∀ g ∈ M, ∀ h ∈ M, g ≤ h → w {h} ≤ w {g}

/-- The sorted value sequence of an ordered valuation, extended by zero. -/
noncomputable def xs (w : Finset (Fin m) → ℝ) (M : Finset (Fin m)) (d : Fin m) (p : ℕ) : ℝ :=
  if p < M.card then w {ePos M d p} else 0

lemma xs_of_lt {w : Finset (Fin m) → ℝ} {M : Finset (Fin m)} {d : Fin m} {p : ℕ}
    (h : p < M.card) : xs w M d p = w {ePos M d p} := if_pos h

lemma xs_of_ge {w : Finset (Fin m) → ℝ} {M : Finset (Fin m)} {d : Fin m} {p : ℕ}
    (h : M.card ≤ p) : xs w M d p = 0 := if_neg (by omega)

lemma xs_nonneg {w : Finset (Fin m) → ℝ} (hw : Add1 w) (M : Finset (Fin m)) (d : Fin m)
    (p : ℕ) : 0 ≤ xs w M d p := by
  unfold xs; split_ifs
  · exact hw.sing_nonneg _
  · exact le_rfl

lemma xs_anti {w : Finset (Fin m) → ℝ} (hw : Add1 w) {M : Finset (Fin m)} (ho : Ord w M)
    (d : Fin m) : Antitone (xs w M d) := by
  intro p q hpq
  by_cases hq : q < M.card
  · have hp : p < M.card := lt_of_le_of_lt hpq hq
    rw [xs_of_lt hp, xs_of_lt hq]
    exact ho _ (ePos_mem hp) _ (ePos_mem hq) ((ePos_le_iff hp hq).mpr hpq)
  · rw [xs_of_ge (by omega)]; exact xs_nonneg hw M d p

/-! ### Sorting permutations -/

lemma exists_sort (w : Finset (Fin m) → ℝ) (M : Finset (Fin m)) :
    ∃ τ : Fin m → Fin m, Set.BijOn τ M M ∧ ∀ g ∈ M, ∀ h ∈ M, g ≤ h → w {τ h} ≤ w {τ g} := by
  classical
  set I := M.orderIsoOfFin rfl with hI
  let F : Fin M.card → ℝ := fun p => - w {(I p).1}
  let σ := Tuple.sort F
  have hmono := Tuple.monotone_sort F
  refine ⟨fun g => if hg : g ∈ M then (I (σ (I.symm ⟨g, hg⟩))).1 else g, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    have hg' : g ∈ M := hg
    simp only [dif_pos hg']
    exact (I _).2
  · intro g hg h hh e
    have hg' : g ∈ M := hg
    have hh' : h ∈ M := hh
    simp only [dif_pos hg', dif_pos hh'] at e
    have e1 := I.injective (Subtype.ext e)
    have e2 := σ.injective e1
    have e3 := I.symm.injective e2
    exact congrArg Subtype.val e3
  · intro y hy
    have hy' : y ∈ M := hy
    refine ⟨(I (σ.symm (I.symm ⟨y, hy'⟩))).1, (I _).2, ?_⟩
    simp only [dif_pos (I _).2]
    simp
  · intro g hg h hh hgh
    simp only [dif_pos hg, dif_pos hh]
    have h1 : I.symm ⟨g, hg⟩ ≤ I.symm ⟨h, hh⟩ := I.symm.monotone hgh
    have h2 := hmono h1
    simp only [Function.comp, F, neg_le_neg_iff] at h2
    exact h2

/-! ### Picking-sequence transfer (Bouveret–Lemaître) -/

lemma picking_aux {n : ℕ} (v w : Fin n → Finset (Fin m) → ℝ) (M : Finset (Fin m))
    (τ : Fin n → Fin m → Fin m) (hτ : ∀ i, Set.BijOn (τ i) M M)
    (hw : ∀ i, ∀ g ∈ M, w i {g} = v i {τ i g}) (hord : ∀ i, Ord (w i) M)
    (A' : Fin m → Fin n) :
    ∀ P : Finset (Fin m), P ⊆ M → (∀ g ∈ P, ∀ g' ∈ M, g' ≤ g → g' ∈ P) →
      ∃ π : Fin m → Fin m, Set.InjOn π P ∧ (∀ g ∈ P, π g ∈ M) ∧
        ∀ g ∈ P, w (A' g) {g} ≤ v (A' g) {π g} := by
  classical
  intro P
  induction P using Finset.induction_on_max with
  | empty =>
    intro _ _
    exact ⟨id, by simp, by simp, by simp⟩
  | insert c P0 hlt ih =>
    intro hPM hdown
    have hcP0 : c ∉ P0 := fun h => lt_irrefl _ (hlt c h)
    have hP0M : P0 ⊆ M := fun g hg => hPM (Finset.mem_insert_of_mem hg)
    have hdown0 : ∀ g ∈ P0, ∀ g' ∈ M, g' ≤ g → g' ∈ P0 := by
      intro g hg g' hg' hle
      have := hdown g (Finset.mem_insert_of_mem hg) g' hg' hle
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd (h ▸ hle) (not_le.mpr (hlt g hg))
      · exact h
    obtain ⟨π0, hinj0, hmap0, hval0⟩ := ih hP0M hdown0
    set a := A' c
    have hcM : c ∈ M := hPM (Finset.mem_insert_self _ _)
    set D := M.filter (fun g => g ≤ c) with hD
    have hDcard : D.card = P0.card + 1 := by
      have : D = insert c P0 := by
        ext g
        simp only [hD, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hgM, hgc⟩
          have := hdown c (Finset.mem_insert_self _ _) g hgM hgc
          exact Finset.mem_insert.mp this
        · rintro (rfl | hg)
          · exact ⟨hcM, le_rfl⟩
          · exact ⟨hP0M hg, (hlt g hg).le⟩
      rw [this, Finset.card_insert_of_notMem hcP0]
    have hcard : (P0.image π0).card < (D.image (τ a)).card := by
      rw [Finset.card_image_of_injOn (fun x hx y hy h =>
        (hτ a).injOn (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 h), hDcard]
      exact Nat.lt_succ_of_le Finset.card_image_le
    obtain ⟨h, hhD, hhn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    obtain ⟨g', hg'D, rfl⟩ := Finset.mem_image.mp hhD
    obtain ⟨hg'M, hg'c⟩ := Finset.mem_filter.mp hg'D
    refine ⟨Function.update π0 c (τ a g'), ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · have hyc : y ≠ x := fun h => hcP0 (h ▸ hy)
        rw [Function.update_self, Function.update_of_ne hyc] at hxy
        exact absurd (Finset.mem_image.mpr ⟨y, hy, hxy.symm⟩) hhn
      · have hxc : x ≠ y := fun h => hcP0 (h ▸ hx)
        rw [Function.update_self, Function.update_of_ne hxc] at hxy
        exact absurd (Finset.mem_image.mpr ⟨x, hx, hxy⟩) hhn
      · have hxc : x ≠ c := fun h => hcP0 (h ▸ hx)
        have hyc : y ≠ c := fun h => hcP0 (h ▸ hy)
        rw [Function.update_of_ne hxc, Function.update_of_ne hyc] at hxy
        exact hinj0 hx hy hxy
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · rw [Function.update_self]; exact (hτ a).mapsTo hg'M
      · have hgc : g ≠ c := fun h => hcP0 (h ▸ hg)
        rw [Function.update_of_ne hgc]; exact hmap0 g hg
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · rw [Function.update_self, ← hw a g' hg'M]
        exact hord a _ hg'M _ hcM hg'c
      · have hgc : g ≠ c := fun h => hcP0 (h ▸ hg)
        rw [Function.update_of_ne hgc]; exact hval0 g hg

/-- Allocation transfer from an ordered instance back to the original one. -/
lemma picking {n : ℕ} (v w : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (hw' : IsAdditive w) (M : Finset (Fin m))
    (τ : Fin n → Fin m → Fin m) (hτ : ∀ i, Set.BijOn (τ i) M M)
    (hw : ∀ i, ∀ g ∈ M, w i {g} = v i {τ i g}) (hord : ∀ i, Ord (w i) M)
    (A' : Fin m → Fin n) :
    ∃ A : Fin m → Fin n, (∀ b ∈ M, ∃ g ∈ M, A b = A' g) ∧
      ∀ i, w i (M.filter (fun b => A' b = i)) ≤ v i (M.filter (fun b => A b = i)) := by
  classical
  obtain ⟨π, hinj, hmap, hval⟩ :=
    picking_aux v w M τ hτ hw hord A' M le_rfl (fun g _ g' hg' _ => hg')
  have hbij : Set.BijOn π M M :=
    (Set.Finite.injOn_iff_bijOn_of_mapsTo (Finset.finite_toSet M)
      (fun g hg => hmap g hg)).mp hinj
  let A : Fin m → Fin n := fun b =>
    if h : ∃ g ∈ M, π g = b then A' (Classical.choose h) else A' b
  have hA : ∀ g ∈ M, A (π g) = A' g := by
    intro g hg
    have hex : ∃ g' ∈ M, π g' = π g := ⟨g, hg, rfl⟩
    simp only [A, dif_pos hex]
    have := (Classical.choose_spec hex)
    rw [hinj this.1 hg this.2]
  refine ⟨A, ?_, ?_⟩
  · intro b hb
    obtain ⟨g, hg, rfl⟩ := hbij.surjOn hb
    exact ⟨g, hg, hA g hg⟩
  · intro i
    have hsub : (M.filter (fun b => A' b = i)).image π ⊆ M.filter (fun b => A b = i) := by
      intro b hb
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hgM, hgi⟩ := Finset.mem_filter.mp hg
      exact Finset.mem_filter.mpr ⟨hmap g hgM, by rw [hA g hgM, hgi]⟩
    refine le_trans ?_ ((add1_of hv i).mono hsub)
    rw [(add1_of hw' i).1, (add1_of hv i).1, Finset.sum_image (fun x hx y hy h =>
      hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 h)]
    refine Finset.sum_le_sum (fun g hg => ?_)
    obtain ⟨hgM, hgi⟩ := Finset.mem_filter.mp hg
    have := hval g hgM
    rw [hgi] at this
    exact this

/-- MMS is invariant under re-labelling goods by a bijection of `M`. -/
lemma mms_le_of_bij {w v : Finset (Fin m) → ℝ} (hv : Add1 v) (hw : Add1 w) {k : ℕ}
    (hk : 0 < k) (M : Finset (Fin m)) (τ : Fin m → Fin m) (hτ : Set.BijOn τ M M)
    (hwv : ∀ g ∈ M, w {g} = v {τ g}) : mms v k M ≤ mms w k M := by
  classical
  obtain ⟨f, hf⟩ := mms_attained v hk M
  refine le_mms_of_labels w hk M (fun g => f (τ g)) _ (fun j => (hf j).trans (le_of_eq ?_))
  have himg : (M.filter (fun g => f (τ g) = j)).image τ = M.filter (fun h => f h = j) := by
    ext h
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨g, ⟨hgM, hgj⟩, rfl⟩
      exact ⟨hτ.mapsTo hgM, hgj⟩
    · rintro ⟨hhM, hhj⟩
      obtain ⟨g, hgM, rfl⟩ := hτ.surjOn hhM
      exact ⟨g, ⟨hgM, hhj⟩, rfl⟩
  rw [← himg, hv.1, hw.1, Finset.sum_image (fun x hx y hy h =>
    hτ.injOn (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 h)]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [hwv g (Finset.mem_filter.mp hg).1]

/-- If `ŵ ≤ z` pointwise with `z` ordered, the sorted version `u` of `ŵ` is also `≤ z`. -/
lemma sorted_dom (z u wh : Finset (Fin m) → ℝ) (M : Finset (Fin m)) (τ : Fin m → Fin m)
    (hτ : Set.BijOn τ M M) (hu : ∀ g ∈ M, u {g} = wh {τ g}) (huo : Ord u M)
    (hzo : Ord z M) (hdom : ∀ h ∈ M, wh {h} ≤ z {h}) : ∀ g ∈ M, u {g} ≤ z {g} := by
  classical
  intro g hg
  by_contra hlt
  push_neg at hlt
  set D := M.filter (fun g' => g' ≤ g)
  set Dl := M.filter (fun g' => g' < g)
  have hsub : D.image τ ⊆ Dl := by
    intro h hh
    obtain ⟨g', hg'D, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hg'M, hg'g⟩ := Finset.mem_filter.mp hg'D
    have hhM := hτ.mapsTo hg'M
    refine Finset.mem_filter.mpr ⟨hhM, ?_⟩
    by_contra hge
    push_neg at hge
    have h1 := hzo _ hg _ hhM hge
    have h2 := hdom _ hhM
    have h3 := huo _ hg'M _ hg hg'g
    rw [hu g' hg'M] at h3
    linarith
  have hc1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (fun x hx y hy h =>
    hτ.injOn (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 h)] at hc1
  have hDeq : D = insert g Dl := by
    ext x
    simp only [D, Dl, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxg⟩
      rcases eq_or_lt_of_le hxg with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (rfl | ⟨hx, hxg⟩)
      · exact ⟨hg, le_rfl⟩
      · exact ⟨hx, hxg.le⟩
  have hc2 : D.card ≤ Dl.card := hc1
  rw [hDeq, Finset.card_insert_of_notMem (by simp [Dl])] at hc2
  omega

end MMS34

-- ===== part B =====

set_option autoImplicit false

namespace MMS34

open Finset

/-- An ordered, normalized, totally-3/4-irreducible value sequence for one agent:
`n` bundles, `M` goods at positions `0, …, M-1`, values `x p`. -/
structure ONI (n M : ℕ) (x : ℕ → ℝ) : Prop where
  npos : 0 < n
  card : 2 * n ≤ M
  anti : Antitone x
  nonneg : ∀ p, 0 ≤ x p
  part : ∃ f : ℕ → Fin n, ∀ q, ∑ p ∈ (range M).filter (fun p => f p = q), x p = 1
  h1 : x 0 < 3 / 4
  h2 : x (n - 1) + x n < 3 / 4
  h3 : ∀ p, 2 * n ≤ p → x p < 1 / 4
  h4 : ∀ p, 2 * n ≤ p → x 0 + x p < 3 / 4

section
variable {n M : ℕ} {x : ℕ → ℝ}

lemma ONI.lt34 (hx : ONI n M x) (p : ℕ) : x p < 3 / 4 :=
  lt_of_le_of_lt (hx.anti (Nat.zero_le p)) hx.h1

lemma ONI.total (hx : ONI n M x) : ∑ p ∈ range M, x p = n := by
  obtain ⟨f, hf⟩ := hx.part
  rw [← Finset.sum_fiberwise (range M) f x]
  simp [hf]

lemma sum_ge_card_mul {S : Finset ℕ} {c : ℝ} (h : ∀ p ∈ S, c ≤ x p) :
    (S.card : ℝ) * c ≤ ∑ p ∈ S, x p := by
  have := Finset.card_nsmul_le_sum S x c h
  simpa [nsmul_eq_mul] using this

/-- Two goods of total value `> 1` cannot share a bundle of the normalized partition. -/
lemma ONI.sep (hx : ONI n M x) (f : ℕ → Fin n)
    (hf : ∀ q, ∑ p ∈ (range M).filter (fun p => f p = q), x p = 1)
    {j j' : ℕ} (hj : j < M) (hj' : j' < M) (hne : j ≠ j') (hgt : 1 < x j + x j') :
    f j ≠ f j' := by
  intro heq
  have hsub : ({j, j'} : Finset ℕ) ⊆ (range M).filter (fun p => f p = f j) := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp [hj]
    · simp [hj', heq]
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hx.nonneg p)
  rw [hf, Finset.sum_pair hne] at this
  linarith

lemma pair_sum {k : ℕ} (hk : k < n) :
    ∑ p ∈ ({k, 2 * n - 1 - k} : Finset ℕ), x p = x k + x (2 * n - 1 - k) := by
  rw [Finset.sum_pair (by omega)]

lemma bags_sum (n : ℕ) (x : ℕ → ℝ) :
    ∑ k ∈ range n, (x k + x (2 * n - 1 - k)) = ∑ p ∈ range (2 * n), x p := by
  rw [Finset.sum_add_distrib, show 2 * n = n + n by ring, Finset.sum_range_add]
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [mem_range] at hk
  congr 1
  omega

/-- AGST Lemma 6. -/
lemma ONI.lemma6 (hx : ONI n M x) {k : ℕ} (hk : k < n)
    (hgt : 1 < x k + x (2 * n - 1 - k)) : x (2 * n - 1 - k) ≤ 1 / 3 := by
  classical
  obtain ⟨f, hf⟩ := hx.part
  have hM := hx.card
  have sep : ∀ j ≤ k, ∀ j' ≤ 2 * n - 1 - k, j ≠ j' → f j ≠ f j' := by
    intro j hj j' hj' hne
    refine hx.sep f hf (by omega) (by omega) hne ?_
    have := hx.anti hj
    have := hx.anti hj'
    linarith
  set I := (range (k + 1)).image f with hI
  have hIcard : I.card = k + 1 := by
    rw [Finset.card_image_of_injOn, card_range]
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    exact sep a (by omega) b (by omega) hne hab
  set Q := Ico (k + 1) (2 * n - k) with hQ
  have hmaps : ∀ p ∈ Q, f p ∈ (univ : Finset (Fin n)) \ I := by
    intro p hp
    simp only [hQ, mem_Ico] at hp
    simp only [mem_sdiff, mem_univ, true_and, hI, mem_image, mem_range, not_exists, not_and]
    intro j hj hjp
    exact sep j (by omega) p (by omega) (by omega) hjp
  have hcardt : ((univ : Finset (Fin n)) \ I).card = n - (k + 1) := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hIcard]
  have hpig : ((univ : Finset (Fin n)) \ I).card * 2 < Q.card := by
    rw [hcardt, hQ, Nat.card_Ico]; omega
  obtain ⟨q, _, hq⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hpig
  have hsub : Q.filter (fun p => f p = q) ⊆ (range M).filter (fun p => f p = q) := by
    intro p hp
    simp only [mem_filter, hQ, mem_Ico, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hx.nonneg p)
  rw [hf q] at h1
  have h2 : ((Q.filter (fun p => f p = q)).card : ℝ) * x (2 * n - 1 - k) ≤
      ∑ p ∈ Q.filter (fun p => f p = q), x p := by
    apply sum_ge_card_mul
    intro p hp
    simp only [mem_filter, hQ, mem_Ico] at hp
    exact hx.anti (by omega)
  have h3 : (3 : ℝ) ≤ (Q.filter (fun p => f p = q)).card := by exact_mod_cast hq
  have h0 := hx.nonneg (2 * n - 1 - k)
  nlinarith

/-- Enumerating a finset of naturals increasingly. -/
lemma exists_enum (A : Finset ℕ) :
    ∃ a : ℕ → ℕ, (∀ t < A.card, a t ∈ A) ∧ (∀ t t', t < t' → t' < A.card → a t < a t') ∧
      ∀ F : ℕ → ℝ, ∑ k ∈ A, F k = ∑ t ∈ range A.card, F (a t) := by
  classical
  let e := A.orderEmbOfFin rfl
  let a : ℕ → ℕ := fun t => if h : t < A.card then e ⟨t, h⟩ else 0
  have ha : ∀ t (h : t < A.card), a t = e ⟨t, h⟩ := fun t h => dif_pos h
  have hmem : ∀ t < A.card, a t ∈ A := fun t h => by
    rw [ha t h]; exact Finset.orderEmbOfFin_mem _ _ _
  have hlt : ∀ t t', t < t' → t' < A.card → a t < a t' := by
    intro t t' htt' ht'
    rw [ha t (by omega), ha t' ht']
    exact e.strictMono (show (⟨t, _⟩ : Fin A.card) < ⟨t', ht'⟩ from htt')
  refine ⟨a, hmem, hlt, fun F => ?_⟩
  have himg : (range A.card).image a = A := by
    ext k
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact hmem t ht
    · intro hk
      have : k ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hk
      obtain ⟨⟨t, ht⟩, rfl⟩ := this
      exact ⟨t, ht, ha t ht⟩
  conv_lhs => rw [← himg]
  rw [Finset.sum_image]
  intro t ht t' ht' h
  simp only [coe_range, Set.mem_Iio] at ht ht'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact absurd h (ne_of_lt (hlt t t' h' ht'))
  · exact absurd h (ne_of_gt (hlt t' t h' ht))

lemma enum_shift {a : ℕ → ℕ} {p : ℕ} (hlt : ∀ t t', t < t' → t' < p → a t < a t') :
    ∀ j t, t + j < p → a t + j ≤ a (t + j) := by
  intro j
  induction j with
  | zero => intro t _; simp
  | succ j ih =>
    intro t ht
    have h1 := ih t (by omega)
    have h2 := hlt (t + j) (t + (j + 1)) (by omega) ht
    omega

/-- The no-stuck lemma: the final bag configuration of bag-filling cannot leave an agent
unsatisfied (AGST Lemmas 7–14). -/
theorem no_stuck (hx : ONI n M x) (C : ℕ → Finset ℕ)
    (hsum : ∑ k ∈ range n, ∑ p ∈ C k, x p = ∑ p ∈ range M, x p)
    (hB : ∀ k < n, k ∈ C k ∧ 2 * n - 1 - k ∈ C k)
    (hlow : ∀ k < n, ∀ p ∈ C k, p ≠ k → p ≠ 2 * n - 1 - k → 2 * n ≤ p)
    (hP2 : ∀ k < n, C k = {k, 2 * n - 1 - k} ∨
      ∃ g ∈ C k, g ≠ k ∧ g ≠ 2 * n - 1 - k ∧ ∑ p ∈ (C k).erase g, x p < 3 / 4)
    (hP3 : ∃ k < n, ∑ p ∈ C k, x p < 3 / 4) : False := by
  classical
  have hM := hx.card
  have hn := hx.npos
  set s : ℕ → ℝ := fun k => x k + x (2 * n - 1 - k) with hs
  have hBsub : ∀ k < n, ({k, 2 * n - 1 - k} : Finset ℕ) ⊆ C k := by
    intro k hk p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact (hB p hk).1
    · exact (hB k hk).2
  have hCge : ∀ k < n, s k ≤ ∑ p ∈ C k, x p := by
    intro k hk
    have := Finset.sum_le_sum_of_subset_of_nonneg (hBsub k hk) (fun p _ _ => hx.nonneg p)
    rwa [pair_sum hk] at this
  -- a bag that grew: its value is below 3/4 plus one low good
  have hgrow : ∀ k < n, C k = {k, 2 * n - 1 - k} ∨
      ∃ g, 2 * n ≤ g ∧ ∑ p ∈ C k, x p < 3 / 4 + x g ∧ 3 / 4 > s k := by
    intro k hk
    rcases hP2 k hk with h | ⟨g, hg, hgk, hgk', hlt⟩
    · exact Or.inl h
    · refine Or.inr ⟨g, hlow k hk g hg hgk hgk', ?_, ?_⟩
      · rw [← Finset.add_sum_erase _ _ hg]; linarith
      · have hsub : ({k, 2 * n - 1 - k} : Finset ℕ) ⊆ (C k).erase g := by
          intro p hp
          refine mem_erase.mpr ⟨?_, hBsub k hk hp⟩
          simp only [mem_insert, mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact fun h => hgk h.symm
          · exact fun h => hgk' h.symm
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hx.nonneg p)
        rw [pair_sum hk] at this
        simp only [hs]; linarith
  have htot := hx.total
  obtain ⟨k0, hk0, hk0v⟩ := hP3
  by_cases hN1 : ∀ k < n, s k ≤ 1
  · -- Lemma 8
    have hle1 : ∀ k < n, ∑ p ∈ C k, x p ≤ 1 := by
      intro k hk
      rcases hgrow k hk with h | ⟨g, hg, hlt, _⟩
      · rw [h, pair_sum hk]; exact hN1 k hk
      · have := hx.h3 g hg; linarith
    have hk0r : k0 ∈ range n := mem_range.mpr hk0
    rw [← Finset.add_sum_erase _ _ hk0r] at hsum
    have : ∑ k ∈ (range n).erase k0, ∑ p ∈ C k, x p ≤ ∑ k ∈ (range n).erase k0, (1 : ℝ) :=
      Finset.sum_le_sum (fun k hk => hle1 k (mem_range.mp (mem_of_mem_erase hk)))
    rw [Finset.sum_const, card_erase_of_mem hk0r, card_range, nsmul_eq_mul, mul_one] at this
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at this
    linarith
  push_neg at hN1
  obtain ⟨t, ht, hst⟩ := hN1
  have L6 : ∀ k < n, 1 < s k → x (2 * n - 1 - k) ≤ 1 / 3 := fun k hk h => hx.lemma6 hk h
  have hxt : 2 / 3 < x t := by have := L6 t ht hst; simp only [hs] at hst; linarith
  have L9 : ∀ p, 2 * n ≤ p → x p < 1 / 12 := by
    intro p hp
    have := hx.h4 p hp
    have := hx.anti (Nat.zero_le t)
    linarith
  have L13 : ∀ k < n, 1 / 2 < s k := by
    intro k hk
    by_cases hkt : k ≤ t
    · have h1 := hx.anti hkt
      have h2 := hx.nonneg (2 * n - 1 - k)
      simp only [hs]; linarith
    · have hyt : 1 / 4 < x (2 * n - 1 - t) := by
        have := hx.lt34 t; simp only [hs] at hst; linarith
      have h1 : x (2 * n - 1 - t) ≤ x (2 * n - 1 - k) := hx.anti (by omega)
      have h2 : x (2 * n - 1 - k) ≤ x k := hx.anti (by omega)
      simp only [hs]; linarith
  -- bags of value ≥ 3/4 never grow
  have hfix : ∀ k < n, 3 / 4 ≤ s k → ∑ p ∈ C k, x p = s k := by
    intro k hk hk34
    rcases hgrow k hk with h | ⟨g, _, _, hlt⟩
    · rw [h, pair_sum hk]
    · linarith
  have hsmall : ∀ k < n, s k < 3 / 4 → ∑ p ∈ C k, x p ≤ 5 / 6 := by
    intro k hk hk34
    rcases hgrow k hk with h | ⟨g, hg, hlt, _⟩
    · rw [h, pair_sum hk]; simp only [hs] at hk34; linarith
    · have := L9 g hg; linarith
  -- the shift ℓ
  have hex : ∃ l, ∀ k, l ≤ k → k < n → x k + x (2 * n - 1 - k + l) ≤ 1 :=
    ⟨n, fun k hk hk' => absurd hk' (by omega)⟩
  set l := Nat.find hex with hl
  have hlspec : ∀ k, l ≤ k → k < n → x k + x (2 * n - 1 - k + l) ≤ 1 := Nat.find_spec hex
  have hl1 : 1 ≤ l := by
    by_contra h0
    have : l = 0 := by omega
    have := hlspec t (by omega) ht
    rw [‹l = 0›, Nat.add_zero] at this
    simp only [hs] at hst
    linarith
  -- Lemma 11
  set Ap := (range n).filter (fun k => 1 < s k) with hAp
  have hApne : t ∈ Ap := mem_filter.mpr ⟨mem_range.mpr ht, hst⟩
  have hApmem : ∀ k ∈ Ap, k < n ∧ 1 < s k := fun k hk => by
    simp only [hAp, mem_filter, mem_range] at hk; exact hk
  have L11 : ∑ k ∈ Ap, s k < Ap.card + l / 12 := by
    by_cases hpl : Ap.card ≤ l
    · have : ∑ k ∈ Ap, s k < ∑ k ∈ Ap, (13 / 12 : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨t, hApne⟩
        intro k hk
        have h1 := hx.lt34 k
        have h2 := L6 k (hApmem k hk).1 (hApmem k hk).2
        simp only [hs]; linarith
      rw [Finset.sum_const, nsmul_eq_mul] at this
      have : (Ap.card : ℝ) ≤ l := by exact_mod_cast hpl
      linarith
    · push_neg at hpl
      obtain ⟨a, hamem, halt, hasum⟩ := exists_enum Ap
      set p := Ap.card
      have hshift := enum_shift halt
      have hsplit : ∑ k ∈ Ap, s k = ∑ t ∈ range p, x (a t) + ∑ t ∈ range p, x (2 * n - 1 - a t) := by
        rw [hasum s, ← Finset.sum_add_distrib]
      have hpe : p = l + (p - l) := by omega
      have hs1 : ∑ t ∈ range p, x (a t) =
          ∑ t ∈ range l, x (a t) + ∑ t ∈ range (p - l), x (a (l + t)) := by
        conv_lhs => rw [hpe]
        rw [Finset.sum_range_add]
      have hpe' : p = (p - l) + l := by omega
      have hs2 : ∑ t ∈ range p, x (2 * n - 1 - a t) =
          ∑ t ∈ range (p - l), x (2 * n - 1 - a t) +
            ∑ t ∈ range l, x (2 * n - 1 - a (p - l + t)) := by
        conv_lhs => rw [hpe']
        rw [Finset.sum_range_add]
      have hA : ∑ t ∈ range l, x (a t) < ∑ t ∈ range l, (3 / 4 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty ⟨0, mem_range.mpr (by omega)⟩
          (fun t _ => hx.lt34 _)
      have hB' : ∑ t ∈ range l, x (2 * n - 1 - a (p - l + t)) ≤ ∑ t ∈ range l, (1 / 3 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        simp only [mem_range] at ht
        have hm := hApmem _ (hamem (p - l + t) (by omega))
        exact L6 _ hm.1 hm.2
      have hC' : ∑ t ∈ range (p - l), (x (a (l + t)) + x (2 * n - 1 - a t)) ≤
          ∑ t ∈ range (p - l), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        simp only [mem_range] at ht
        have h1 := hshift l t (by omega)
        have h1' : a t + l ≤ a (l + t) := by rw [Nat.add_comm l t]; exact h1
        have hm := hApmem _ (hamem (l + t) (by omega))
        have hk := hlspec (a t + l) (by omega) (by omega)
        have h2 : x (a (l + t)) ≤ x (a t + l) := hx.anti h1'
        have h3 : 2 * n - 1 - (a t + l) + l = 2 * n - 1 - a t := by omega
        rw [h3] at hk
        linarith
      rw [Finset.sum_add_distrib] at hC'
      simp only [Finset.sum_const, card_range, nsmul_eq_mul, mul_one] at hA hB' hC'
      have hcast : ((p - l : ℕ) : ℝ) = (p : ℝ) - l := by rw [Nat.cast_sub (by omega)]
      rw [hcast] at hC'
      rw [hsplit, hs1, hs2]
      linarith
  -- Lemma 12
  have L12 : (l : ℝ) / 4 < ∑ p ∈ Ico (2 * n) M, x p := by
    obtain ⟨f, hf⟩ := hx.part
    have hmin : ¬ ∀ k, l - 1 ≤ k → k < n → x k + x (2 * n - 1 - k + (l - 1)) ≤ 1 :=
      Nat.find_min hex (by omega)
    push_neg at hmin
    obtain ⟨k, hk1, hk2, hk3⟩ := hmin
    obtain ⟨T, hT⟩ : ∃ T, T = 2 * n - 1 - k + (l - 1) := ⟨_, rfl⟩
    rw [← hT] at hk3
    have hT1 : T ≤ 2 * n - 1 := by omega
    have hT2 : k < T := by omega
    have sep : ∀ j ≤ k, ∀ j' ≤ T, j ≠ j' → f j ≠ f j' := by
      intro j hj j' hj' hne
      refine hx.sep f hf (by omega) (by omega) hne ?_
      have := hx.anti hj
      have := hx.anti hj'
      linarith
    obtain ⟨E, hE⟩ : ∃ E : Finset (Fin n), E = ((range (k + 1)).image f).filter
        (fun q => ∃ p ∈ Ico (T + 1) (2 * n), f p = q) := ⟨_, rfl⟩
    have hEcard : E.card ≤ k + 1 - l := by
      have hsub : E ⊆ (Ico (T + 1) (2 * n)).image f := by
        intro q hq
        simp only [hE, mem_filter] at hq
        obtain ⟨p, hp, hpq⟩ := hq.2
        exact mem_image.mpr ⟨p, hp, hpq⟩
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      rw [Nat.card_Ico] at this
      omega
    obtain ⟨G, hG⟩ : ∃ G : Finset ℕ, G = (range (k + 1)).filter (fun j => f j ∉ E) :=
      ⟨_, rfl⟩
    have hGcard : l ≤ G.card := by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := range (k + 1)) (fun j => f j ∉ E)
      have h2 : ((range (k + 1)).filter (fun j => ¬ f j ∉ E)).card ≤ E.card := by
        apply Finset.card_le_card_of_injOn f
        · intro j hj
          simp only [coe_filter, Set.mem_ofPred_eq, not_not] at hj
          exact hj.2
        · intro a ha b hb hab
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
          by_contra hne
          exact sep a (by omega) b (by omega) hne hab
      rw [card_range] at h1
      rw [hG]
      omega
    -- each good bundle has low part worth > 1/4
    have hlowpart : ∀ j ∈ G,
        ∑ p ∈ (Ico (2 * n) M).filter (fun p => f p = f j), x p = 1 - x j := by
      intro j hj
      rw [hG] at hj
      obtain ⟨hjr, hjE⟩ := mem_filter.mp hj
      simp only [mem_range] at hjr
      have hsplit : (range M).filter (fun p => f p = f j) =
          (range (2 * n)).filter (fun p => f p = f j) ∪
            (Ico (2 * n) M).filter (fun p => f p = f j) := by
        rw [← Finset.filter_union]
        congr 1
        ext p
        simp only [mem_range, mem_union, mem_Ico]
        omega
      have hdisj : Disjoint ((range (2 * n)).filter (fun p => f p = f j))
          ((Ico (2 * n) M).filter (fun p => f p = f j)) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive _ _ _
      have hhigh : (range (2 * n)).filter (fun p => f p = f j) = {j} := by
        ext p
        simp only [mem_filter, mem_range, mem_singleton]
        constructor
        · rintro ⟨hp, hpj⟩
          by_contra hne
          by_cases hpk : p ≤ k
          · exact sep p hpk j (by omega) hne hpj
          by_cases hpT : p ≤ T
          · exact sep j (by omega) p hpT (fun h => hne h.symm) hpj.symm
          · apply hjE
            rw [hE]
            simp only [Finset.mem_filter, Finset.mem_image]
            exact ⟨⟨j, mem_range.mpr hjr, rfl⟩, p, mem_Ico.mpr ⟨by omega, hp⟩, hpj⟩
        · rintro rfl; exact ⟨by omega, rfl⟩
      have := hf (f j)
      rw [hsplit, Finset.sum_union hdisj, hhigh, Finset.sum_singleton] at this
      linarith
    have hinjG : Set.InjOn f G := by
      intro a ha b hb hab
      rw [hG] at ha hb
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
      by_contra hne
      exact sep a (by omega) b (by omega) hne hab
    have hle : ∑ j ∈ G, ∑ p ∈ (Ico (2 * n) M).filter (fun p => f p = f j), x p ≤
        ∑ p ∈ Ico (2 * n) M, x p := by
      rw [← Finset.sum_image (f := fun q => ∑ p ∈ (Ico (2 * n) M).filter (fun p => f p = q), x p)
        hinjG]
      rw [Finset.sum_fiberwise_eq_sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => hx.nonneg p)
    have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
    have hgt : ∑ j ∈ G, (1 / 4 : ℝ) < ∑ j ∈ G,
        ∑ p ∈ (Ico (2 * n) M).filter (fun p => f p = f j), x p := by
      apply Finset.sum_lt_sum_of_nonempty hGne
      intro j hj
      rw [hlowpart j hj]
      have := hx.lt34 j
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at hgt
    have : (l : ℝ) ≤ G.card := by exact_mod_cast hGcard
    linarith
  -- Lemma 14
  set Am := (range n).filter (fun k => s k < 3 / 4) with hAm
  set A0 := (range n).filter (fun k => 3 / 4 ≤ s k ∧ s k ≤ 1) with hA0
  have hpartn : ∀ F : ℕ → ℝ, ∑ k ∈ range n, F k =
      ∑ k ∈ Am, F k + ∑ k ∈ Ap, F k + ∑ k ∈ A0, F k := by
    intro F
    rw [← Finset.sum_filter_add_sum_filter_not (range n) (fun k => s k < 3 / 4)]
    rw [← Finset.sum_filter_add_sum_filter_not ((range n).filter (fun k => ¬ s k < 3 / 4))
      (fun k => 1 < s k)]
    rw [Finset.filter_filter, Finset.filter_filter]
    have e1 : (range n).filter (fun k => ¬ s k < 3 / 4 ∧ 1 < s k) = Ap := by
      rw [hAp]; congr 1; ext k; constructor
      · exact fun h => h.2
      · intro h; exact ⟨by linarith, h⟩
    have e2 : (range n).filter (fun k => ¬ s k < 3 / 4 ∧ ¬ 1 < s k) = A0 := by
      rw [hA0]; congr 1; ext k; push_neg; exact Iff.rfl
    rw [e1, e2]; ring
  have hcardn : (n : ℝ) = Am.card + Ap.card + A0.card := by
    have := hpartn (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this
  have hsumC := hpartn (fun k => ∑ p ∈ C k, x p)
  rw [hsum, htot] at hsumC
  have hAm_le : ∑ k ∈ Am, ∑ p ∈ C k, x p ≤ ∑ k ∈ Am, (5 / 6 : ℝ) := by
    apply Finset.sum_le_sum; intro k hk
    simp only [hAm, mem_filter, mem_range] at hk
    exact hsmall k hk.1 hk.2
  have hAp_eq : ∑ k ∈ Ap, ∑ p ∈ C k, x p = ∑ k ∈ Ap, s k := by
    apply Finset.sum_congr rfl; intro k hk
    exact hfix k (hApmem k hk).1 (by linarith [(hApmem k hk).2])
  have hA0_le : ∑ k ∈ A0, ∑ p ∈ C k, x p ≤ ∑ k ∈ A0, (1 : ℝ) := by
    apply Finset.sum_le_sum; intro k hk
    simp only [hA0, mem_filter, mem_range] at hk
    rw [hfix k hk.1 hk.2.1]; exact hk.2.2
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hAm_le hA0_le
  have hAmsmall : (Am.card : ℝ) < l / 2 := by linarith
  -- low goods are exactly the growth of the bags in Am
  have hlowsum : ∑ p ∈ Ico (2 * n) M, x p = ∑ k ∈ range n, (∑ p ∈ C k, x p - s k) := by
    rw [Finset.sum_sub_distrib, hsum, bags_sum n x, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (2 * n)) hM]
    ring
  rw [hpartn (fun k => ∑ p ∈ C k, x p - s k)] at hlowsum
  have hz1 : ∑ k ∈ Ap, (∑ p ∈ C k, x p - s k) = 0 := by
    apply Finset.sum_eq_zero; intro k hk
    rw [hfix k (hApmem k hk).1 (by linarith [(hApmem k hk).2])]; ring
  have hz2 : ∑ k ∈ A0, (∑ p ∈ C k, x p - s k) = 0 := by
    apply Finset.sum_eq_zero; intro k hk
    simp only [hA0, mem_filter, mem_range] at hk
    rw [hfix k hk.1 hk.2.1]; ring
  have hz3 : ∑ k ∈ Am, (∑ p ∈ C k, x p - s k) ≤ ∑ k ∈ Am, (1 / 3 : ℝ) := by
    apply Finset.sum_le_sum; intro k hk
    simp only [hAm, mem_filter, mem_range] at hk
    have := hsmall k hk.1 hk.2
    have := L13 k hk.1
    linarith
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hz3
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
  linarith

end

end MMS34

-- ===== part D =====

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

namespace MMS34

open Finset

variable {m : ℕ}

/-- Dropping the bundle `q` of a labelling, when all goods of `S` lie in bundle `q`. -/
lemma mms_drop {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (M S : Finset (Fin m))
    (f : Fin m → Fin (k + 2)) (q : Fin (k + 2)) (hS : ∀ g ∈ S, f g = q) (c : ℝ)
    (hc : ∀ l, l ≠ q → c ≤ w (M.filter (fun g => f g = l))) :
    c ≤ mms w (k + 1) (M \ S) := by
  classical
  refine le_mms_of_family hw (Nat.succ_pos k) (M \ S)
    (fun a => M.filter (fun g => f g = q.succAbove a)) ?_ ?_ c ?_
  · intro a b hab
    rw [Finset.disjoint_left]
    intro g ha hb
    simp only [mem_filter] at ha hb
    exact hab (Fin.succAbove_right_injective (ha.2.symm.trans hb.2))
  · intro a g hg
    simp only [mem_filter] at hg
    refine mem_sdiff.mpr ⟨hg.1, fun hgS => ?_⟩
    exact Fin.succAbove_ne q a (hg.2.symm.trans (hS g hgS))
  · intro a
    exact hc _ (Fin.succAbove_ne q a)

/-- Swapping a good `s` with a weakly more valuable good `d` of bundle `q` keeps every other
bundle's value from decreasing. -/
lemma swap_bundles {w : Finset (Fin m) → ℝ} (hw : Add1 w) {K : ℕ} (M : Finset (Fin m))
    (f : Fin m → Fin K) (q : Fin K) {s d : Fin m} (hs : s ∈ M) (hd : d ∈ M) (hfd : f d = q)
    (hsd : w {s} ≤ w {d}) (c : ℝ) (hc : ∀ l, l ≠ q → c ≤ w (M.filter (fun g => f g = l))) :
    ∀ l, l ≠ q → c ≤ w (M.filter (fun g => f (Equiv.swap s d g) = l)) := by
  classical
  intro l hl
  refine (hc l hl).trans ?_
  have himg : M.filter (fun g => f (Equiv.swap s d g) = l) =
      (M.filter (fun g => f g = l)).image (Equiv.swap s d) := by
    ext g
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hg, hgl⟩
      refine ⟨Equiv.swap s d g, ⟨?_, hgl⟩, Equiv.swap_apply_self _ _ _⟩
      rcases eq_or_ne g s with rfl | h1
      · rw [Equiv.swap_apply_left]; exact hd
      rcases eq_or_ne g d with rfl | h2
      · rw [Equiv.swap_apply_right]; exact hs
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hg
    · rintro ⟨h, ⟨hh, hhl⟩, rfl⟩
      refine ⟨?_, by rw [Equiv.swap_apply_self]; exact hhl⟩
      rcases eq_or_ne h s with rfl | h1
      · rw [Equiv.swap_apply_left]; exact hd
      rcases eq_or_ne h d with rfl | h2
      · rw [Equiv.swap_apply_right]; exact hs
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hh
  rw [himg, hw.1, hw.1 (Finset.image _ _), Finset.sum_image
    (fun x _ y _ h => (Equiv.swap s d).injective h)]
  refine Finset.sum_le_sum (fun h hh => ?_)
  simp only [mem_filter] at hh
  rcases eq_or_ne h s with rfl | h1
  · rw [Equiv.swap_apply_left]; exact hsd
  rcases eq_or_ne h d with rfl | h2
  · exact absurd (hfd.symm.trans hh.2).symm hl
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Ordered values along positions. -/
lemma ord_pos {w : Finset (Fin m) → ℝ} {M : Finset (Fin m)} (ho : Ord w M) (d0 : Fin m)
    {a b : ℕ} (hab : a ≤ b) (hb : b < M.card) : w {ePos M d0 b} ≤ w {ePos M d0 a} :=
  ho _ (ePos_mem (lt_of_le_of_lt hab hb)) _ (ePos_mem hb)
    ((ePos_le_iff (lt_of_le_of_lt hab hb) hb).mpr hab)

lemma swap_apply_other {s d g : Fin m} (h1 : g ≠ s) (h2 : g ≠ d) : Equiv.swap s d g = g :=
  Equiv.swap_apply_of_ne_of_ne h1 h2

/-- R1 validity: removing one good and one bundle. -/
lemma valid_one {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (M : Finset (Fin m))
    (g : Fin m) : mms w (k + 2) M ≤ mms w (k + 1) (M \ {g}) := by
  classical
  obtain ⟨f, hf⟩ := mms_attained w (Nat.succ_pos (k + 1)) M
  exact mms_drop hw M {g} f (f g) (by simp) _ (fun l _ => hf l)

/-- Giving nothing away: `MMS^{k+1} ≤ MMS^{k}`. -/
lemma valid_empty {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (M : Finset (Fin m)) :
    mms w (k + 2) M ≤ mms w (k + 1) (M \ ∅) := by
  classical
  obtain ⟨f, hf⟩ := mms_attained w (Nat.succ_pos (k + 1)) M
  exact mms_drop hw M ∅ f 0 (by simp) _ (fun l _ => hf l)

/-- R2 validity: removing the goods at positions `K-1, K` (0-indexed) for `K = k+2` bundles. -/
lemma valid_two {w : Finset (Fin m) → ℝ} (hw : Add1 w) {M : Finset (Fin m)} (ho : Ord w M)
    {k : ℕ} (d0 : Fin m) (hM : k + 3 ≤ M.card) :
    mms w (k + 2) M ≤
      mms w (k + 1) (M \ {ePos M d0 (k + 1), ePos M d0 (k + 2)}) := by
  classical
  set P := ePos M d0 with hP
  obtain ⟨f, hf⟩ := mms_attained w (Nat.succ_pos (k + 1)) M
  -- pigeonhole among positions 0..k+2
  have hmaps : ∀ p ∈ range (k + 3), (fun p => f (P p)) p ∈ (univ : Finset (Fin (k + 2))) :=
    fun _ _ => mem_univ _
  have hlt : (univ : Finset (Fin (k + 2))).card < (range (k + 3)).card := by simp
  obtain ⟨a', ha', b', hb', hne, hab'⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  simp only [mem_range] at ha' hb'
  obtain ⟨a, b, hab, ha, hb, hfab⟩ : ∃ a b, a < b ∧ a < k + 3 ∧ b < k + 3 ∧ f (P a) = f (P b) := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨a', b', h, ha', hb', hab'⟩
    · exact ⟨b', a', h, hb', ha', hab'.symm⟩
  set q := f (P b)
  have hPinj : ∀ x y, x < M.card → y < M.card → x ≠ y → P x ≠ P y := fun x y hx hy h e =>
    h ((ePos_inj hx hy).mp e)
  -- first swap: position k+2 with b
  set f1 := fun g => f (Equiv.swap (P (k + 2)) (P b) g)
  have hf1 := swap_bundles hw M f q (ePos_mem (by omega)) (ePos_mem (by omega)) rfl
    (ord_pos ho d0 (a := b) (b := k + 2) (by omega) (by omega)) _ (fun l _ => hf l)
  have hf1K : f1 (P (k + 2)) = q := by simp [f1, q]
  have hf1a : f1 (P a) = q := by
    simp only [f1]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hfab
  -- second swap: position k+1 with a
  set f2 := fun g => f1 (Equiv.swap (P (k + 1)) (P a) g)
  have hf2 := swap_bundles hw M f1 q (ePos_mem (by omega)) (ePos_mem (by omega)) hf1a
    (ord_pos ho d0 (a := a) (b := k + 1) (by omega) (by omega)) _ hf1
  have hf2a : f2 (P (k + 1)) = q := by simp [f2, hf1a]
  have hf2b : f2 (P (k + 2)) = q := by
    simp only [f2]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hf1K
  refine mms_drop hw M _ f2 q ?_ _ hf2
  intro g hg
  simp only [mem_insert, mem_singleton] at hg
  rcases hg with rfl | rfl
  · exact hf2a
  · exact hf2b

/-- R3 validity: removing the goods at positions `2K-2, 2K-1, 2K` for `K = k+2` bundles. -/
lemma valid_three {w : Finset (Fin m) → ℝ} (hw : Add1 w) {M : Finset (Fin m)} (ho : Ord w M)
    {k : ℕ} (d0 : Fin m) (hM : 2 * (k + 2) + 1 ≤ M.card) :
    mms w (k + 2) M ≤
      mms w (k + 1) (M \ {ePos M d0 (2 * (k + 2) - 2), ePos M d0 (2 * (k + 2) - 1),
        ePos M d0 (2 * (k + 2))}) := by
  classical
  set P := ePos M d0 with hP
  obtain ⟨f, hf⟩ := mms_attained w (Nat.succ_pos (k + 1)) M
  have hmaps : ∀ p ∈ range (2 * (k + 2) + 1), (fun p => f (P p)) p ∈
      (univ : Finset (Fin (k + 2))) := fun _ _ => mem_univ _
  have hlt : (univ : Finset (Fin (k + 2))).card * 2 < (range (2 * (k + 2) + 1)).card := by
    simp only [card_univ, Fintype.card_fin, card_range]; omega
  obtain ⟨q, _, hq⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set F := (range (2 * (k + 2) + 1)).filter (fun p => f (P p) = q) with hF
  -- three smallest elements a < b < c of F
  obtain ⟨a, b, c, hab, hbc, hc, hfa, hfb, hfc⟩ : ∃ a b c, a < b ∧ b < c ∧ c < 2 * (k + 2) + 1 ∧
      f (P a) = q ∧ f (P b) = q ∧ f (P c) = q := by
    obtain ⟨e, he1, he2, he3⟩ := exists_enum F
    have h0 := he1 0 (by omega)
    have h1 := he1 1 (by omega)
    have h2 := he1 2 (by omega)
    simp only [hF, mem_filter, mem_range] at h0 h1 h2
    exact ⟨e 0, e 1, e 2, he2 0 1 (by omega) (by omega), he2 1 2 (by omega) (by omega),
      h2.1, h0.2, h1.2, h2.2⟩
  have hPinj : ∀ x y, x < M.card → y < M.card → x ≠ y → P x ≠ P y := fun x y hx hy h e =>
    h ((ePos_inj hx hy).mp e)
  set K2 := 2 * (k + 2)
  -- swap K2 with c
  set f1 := fun g => f (Equiv.swap (P K2) (P c) g)
  have hf1 := swap_bundles hw M f q (ePos_mem (by omega)) (ePos_mem (by omega)) hfc
    (ord_pos ho d0 (a := c) (b := K2) (by omega) (by omega)) _ (fun l _ => hf l)
  have hf1K : f1 (P K2) = q := by simp [f1, hfc]
  have hf1a : f1 (P a) = q := by
    simp only [f1]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hfa
  have hf1b : f1 (P b) = q := by
    simp only [f1]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hfb
  -- swap K2-1 with b
  set f2 := fun g => f1 (Equiv.swap (P (K2 - 1)) (P b) g)
  have hf2 := swap_bundles hw M f1 q (ePos_mem (by omega)) (ePos_mem (by omega)) hf1b
    (ord_pos ho d0 (a := b) (b := K2 - 1) (by omega) (by omega)) _ hf1
  have hf2K1 : f2 (P (K2 - 1)) = q := by simp [f2, hf1b]
  have hf2K : f2 (P K2) = q := by
    simp only [f2]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hf1K
  have hf2a : f2 (P a) = q := by
    simp only [f2]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hf1a
  -- swap K2-2 with a
  set f3 := fun g => f2 (Equiv.swap (P (K2 - 2)) (P a) g)
  have hf3 := swap_bundles hw M f2 q (ePos_mem (by omega)) (ePos_mem (by omega)) hf2a
    (ord_pos ho d0 (a := a) (b := K2 - 2) (by omega) (by omega)) _ hf2
  have hf3K2 : f3 (P (K2 - 2)) = q := by simp [f3, hf2a]
  have hf3K1 : f3 (P (K2 - 1)) = q := by
    simp only [f3]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hf2K1
  have hf3K : f3 (P K2) = q := by
    simp only [f3]
    rw [swap_apply_other (hPinj _ _ (by omega) (by omega) (by omega))
      (hPinj _ _ (by omega) (by omega) (by omega))]
    exact hf2K
  refine mms_drop hw M _ f3 q ?_ _ hf3
  intro g hg
  simp only [mem_insert, mem_singleton] at hg
  rcases hg with rfl | rfl | rfl
  · exact hf3K2
  · exact hf3K1
  · exact hf3K

/-- R4 validity (AGST Lemma 16): removing the goods `{g₀, g_{2K}}` is valid as soon as
their total value is at most the MMS value. -/
lemma valid_four {w : Finset (Fin m) → ℝ} (hw : Add1 w) {k : ℕ} (M : Finset (Fin m))
    {g h : Fin m} (hg : g ∈ M) (hh : h ∈ M) (hgh : g ≠ h)
    (hsmall : w {g} + w {h} ≤ mms w (k + 2) M) :
    mms w (k + 2) M ≤ mms w (k + 1) (M \ {g, h}) := by
  classical
  obtain ⟨f, hf⟩ := mms_attained w (Nat.succ_pos (k + 1)) M
  set c := mms w (k + 2) M
  by_cases hsame : f g = f h
  · refine mms_drop hw M _ f (f g) ?_ _ (fun l _ => hf l)
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · exact hsame.symm
  -- different bundles: merge them, drop the bundle of `h`
  set qh := f h
  set qg := f g
  set f' : Fin m → Fin (k + 2) := fun x => if f x = qh then qg else f x
  have hf'1 : ∀ x ∈ ({g, h} : Finset (Fin m)), f' x = qg := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp only [f']; rw [if_neg hsame]
    · simp only [f']; rw [if_pos rfl]
  have hmerge : M.filter (fun x => f' x = qg) =
      M.filter (fun x => f x = qg) ∪ M.filter (fun x => f x = qh) := by
    ext x
    simp only [mem_filter, mem_union, f']
    by_cases h1 : f x = qh
    · rw [if_pos h1]
      constructor
      · intro hx; exact Or.inr ⟨hx.1, h1⟩
      · rintro (hx | hx)
        · exact ⟨hx.1, rfl⟩
        · exact ⟨hx.1, rfl⟩
    · rw [if_neg h1]
      constructor
      · intro hx; exact Or.inl hx
      · rintro (hx | hx)
        · exact hx
        · exact absurd hx.2 h1
  have hdisj : Disjoint (M.filter (fun x => f x = qg)) (M.filter (fun x => f x = qh)) :=
    Finset.disjoint_filter.mpr (fun x _ h1 h2 => hsame (h1.symm.trans h2))
  -- the merged bundle minus {g,h}
  refine le_mms_of_family hw (Nat.succ_pos k) (M \ {g, h})
    (fun a => if qh.succAbove a = qg then M.filter (fun x => f' x = qg) \ {g, h}
      else M.filter (fun x => f x = qh.succAbove a)) ?_ ?_ c ?_
  · intro a b hab
    have hne : qh.succAbove a ≠ qh.succAbove b := fun e => hab (Fin.succAbove_right_injective e)
    have key : ∀ l l' : Fin (k + 2), l ≠ l' → l ≠ qh → l' ≠ qh →
        Disjoint (if l = qg then M.filter (fun x => f' x = qg) \ {g, h}
          else M.filter (fun x => f x = l))
          (if l' = qg then M.filter (fun x => f' x = qg) \ {g, h}
          else M.filter (fun x => f x = l')) := by
      intro l l' hll' hl hl'
      rw [Finset.disjoint_left]
      intro x hx hx'
      split_ifs at hx hx' with e1 e2 e2
      · exact hll' (e1.trans e2.symm)
      · simp only [mem_sdiff, mem_filter, f'] at hx hx'
        obtain ⟨⟨_, hx1⟩, _⟩ := hx
        split_ifs at hx1 with e3
        · exact hl' (hx'.2.symm.trans e3)
        · exact e2 (hx'.2.symm.trans hx1)
      · simp only [mem_sdiff, mem_filter, f'] at hx hx'
        obtain ⟨⟨_, hx1⟩, _⟩ := hx'
        split_ifs at hx1 with e3
        · exact hl (hx.2.symm.trans e3)
        · exact e1 (hx.2.symm.trans hx1)
      · simp only [mem_filter] at hx hx'
        exact hll' (hx.2.symm.trans hx'.2)
    exact key _ _ hne (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _)
  · intro a x hx
    split_ifs at hx with e
    · simp only [mem_sdiff, mem_filter] at hx
      exact mem_sdiff.mpr ⟨hx.1.1, hx.2⟩
    · simp only [mem_filter] at hx
      refine mem_sdiff.mpr ⟨hx.1, fun hxS => ?_⟩
      simp only [mem_insert, mem_singleton] at hxS
      rcases hxS with rfl | rfl
      · exact e hx.2.symm
      · exact Fin.succAbove_ne qh a hx.2.symm
  · intro a
    split_ifs with e
    · have hsub : ({g, h} : Finset (Fin m)) ⊆ M.filter (fun x => f' x = qg) := by
        intro x hx
        exact mem_filter.mpr ⟨by
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hg
          · exact hh, hf'1 x hx⟩
      rw [hw.sdiff hsub, hmerge, hw.union hdisj, hw.pair hgh]
      have := hf qg
      have := hf qh
      linarith
    · exact hf _

end MMS34

-- ===== part E =====

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

namespace MMS34

open Finset

variable {m : ℕ}

/-- Summing over the positions of a subset `T ⊆ M`. -/
lemma sum_pos_filter (M : Finset (Fin m)) (d0 : Fin m) (F : Fin m → ℝ) (T : Finset (Fin m))
    (hT : T ⊆ M) :
    ∑ p ∈ (range M.card).filter (fun p => ePos M d0 p ∈ T), F (ePos M d0 p) = ∑ g ∈ T, F g := by
  classical
  have himg : ((range M.card).filter (fun p => ePos M d0 p ∈ T)).image (ePos M d0) = T := by
    ext g
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨p, ⟨_, hp⟩, rfl⟩; exact hp
    · intro hg
      obtain ⟨p, hp, rfl⟩ := ePos_surj (d := d0) (hT hg)
      exact ⟨p, ⟨hp, hg⟩, rfl⟩
  conv_rhs => rw [← himg]
  rw [Finset.sum_image]
  intro x hx y hy h
  simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
  exact (ePos_inj hx.1 hy.1).mp h

lemma sum_xs_filter {u : Finset (Fin m) → ℝ} (hu : Add1 u) (M : Finset (Fin m)) (d0 : Fin m)
    (T : Finset (Fin m)) (hT : T ⊆ M) :
    ∑ p ∈ (range M.card).filter (fun p => ePos M d0 p ∈ T), xs u M d0 p = u T := by
  rw [hu.1 T, ← sum_pos_filter M d0 (fun g => u {g}) T hT]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [mem_filter, mem_range] at hp
  exact xs_of_lt hp.1

/-- The normalisation of AGST Algorithm 1: each good is divided by the value of its bundle. -/
noncomputable def normv (w : Finset (Fin m) → ℝ) (M : Finset (Fin m)) {K : ℕ}
    (f : Fin m → Fin K) : Finset (Fin m) → ℝ :=
  fun S => ∑ g ∈ S, w {g} / w (M.filter (fun x => f x = f g))

lemma normv_single (w : Finset (Fin m) → ℝ) (M : Finset (Fin m)) {K : ℕ} (f : Fin m → Fin K)
    (g : Fin m) : normv w M f {g} = w {g} / w (M.filter (fun x => f x = f g)) := by
  simp [normv]

lemma normv_add1 {w : Finset (Fin m) → ℝ} (hw : Add1 w) (M : Finset (Fin m)) {K : ℕ}
    (f : Fin m → Fin K) : Add1 (normv w M f) := by
  refine ⟨fun S => ?_, fun S => ?_⟩
  · simp only [normv_single]; rfl
  · exact Finset.sum_nonneg (fun g _ => div_nonneg (hw.2 _) (hw.2 _))

lemma normv_bundle {w : Finset (Fin m) → ℝ} (hw : Add1 w) (M : Finset (Fin m)) {K : ℕ}
    (f : Fin m → Fin K) {c : ℝ} (hc : 0 < c)
    (hf : ∀ j, c ≤ w (M.filter (fun x => f x = j))) (j : Fin K) :
    normv w M f (M.filter (fun x => f x = j)) = 1 := by
  have hpos : 0 < w (M.filter (fun x => f x = j)) := lt_of_lt_of_le hc (hf j)
  have : normv w M f (M.filter (fun x => f x = j)) =
      ∑ g ∈ M.filter (fun x => f x = j), w {g} / w (M.filter (fun x => f x = j)) := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    rw [(mem_filter.mp hg).2]
  rw [this, ← Finset.sum_div, ← hw.1, div_self hpos.ne']

lemma normv_le {w : Finset (Fin m) → ℝ} (hw : Add1 w) (M : Finset (Fin m)) {K : ℕ}
    (f : Fin m → Fin K) {c : ℝ} (hc : 0 < c)
    (hf : ∀ j, c ≤ w (M.filter (fun x => f x = j))) (g : Fin m) :
    normv w M f {g} ≤ w {g} / c := by
  rw [normv_single]
  exact div_le_div_of_nonneg_left (hw.2 _) hc (hf _)

/-- `c · normv ≤ w`. -/
lemma normv_mul_le {w : Finset (Fin m) → ℝ} (hw : Add1 w) (M : Finset (Fin m)) {K : ℕ}
    (f : Fin m → Fin K) {c : ℝ} (hc : 0 < c)
    (hf : ∀ j, c ≤ w (M.filter (fun x => f x = j))) (S : Finset (Fin m)) :
    c * normv w M f S ≤ w S := by
  rw [(normv_add1 hw M f).1, hw.1 S, Finset.mul_sum]
  refine Finset.sum_le_sum (fun g _ => ?_)
  have := normv_le hw M f hc hf g
  rw [le_div_iff₀ hc] at this
  linarith

/-- Lemma 3 of AGST: R1-irreducibility forces `2K ≤ |M|`. -/
lemma two_K_le {w : Finset (Fin m) → ℝ} (hw : Add1 w) {M : Finset (Fin m)} (ho : Ord w M)
    {K : ℕ} (hK : 0 < K) (d0 : Fin m) (hc : 0 < mms w K M)
    (I1 : w {ePos M d0 0} < 3 / 4 * mms w K M) : 2 * K ≤ M.card := by
  classical
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf⟩ := mms_attained w hK M
  have hsum : ∑ j : Fin K, (M.filter (fun x => f x = j)).card = M.card :=
    (Finset.card_eq_sum_card_fiberwise (fun x _ => mem_univ (f x))).symm
  have hex : ∃ j : Fin K, (M.filter (fun x => f x = j)).card ≤ 1 := by
    by_contra hne
    push_neg at hne
    have : ∑ j : Fin K, 2 ≤ ∑ j : Fin K, (M.filter (fun x => f x = j)).card :=
      Finset.sum_le_sum (fun j _ => hne j)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  obtain ⟨j, hj⟩ := hex
  have hv := hf j
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, hw.empty] at hv
    linarith
  · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h1
    rw [hg] at hv
    have hgM : g ∈ M := (mem_filter.mp (hg ▸ mem_singleton_self g : g ∈ M.filter _)).1
    obtain ⟨p, hp, rfl⟩ := ePos_surj (d := d0) hgM
    have := ord_pos ho d0 (Nat.zero_le p) hp
    linarith

/-- The per-agent ONI property of the normalised, re-sorted valuation. -/
theorem agent_ONI {w : Finset (Fin m) → ℝ} (hw : Add1 w) {M : Finset (Fin m)} (ho : Ord w M)
    {K : ℕ} (hK : 0 < K) (d0 : Fin m) (hc : 0 < mms w K M)
    (I1 : w {ePos M d0 0} < 3 / 4 * mms w K M)
    (I2 : K + 1 ≤ M.card → w {ePos M d0 (K - 1)} + w {ePos M d0 K} < 3 / 4 * mms w K M)
    (I3 : 2 * K + 1 ≤ M.card → w {ePos M d0 (2 * K - 2)} + w {ePos M d0 (2 * K - 1)} +
      w {ePos M d0 (2 * K)} < 3 / 4 * mms w K M)
    (I4 : 2 * K + 1 ≤ M.card → w {ePos M d0 0} + w {ePos M d0 (2 * K)} < 3 / 4 * mms w K M)
    (f : Fin m → Fin K) (hf : ∀ j, mms w K M ≤ w (M.filter (fun x => f x = j)))
    (τ : Fin m → Fin m) (hτ : Set.BijOn τ M M) (u : Finset (Fin m) → ℝ) (hu : Add1 u)
    (huτ : ∀ g ∈ M, u {g} = normv w M f {τ g}) (huo : Ord u M) :
    ONI K M.card (xs u M d0) := by
  classical
  set c := mms w K M with hcdef
  set P := ePos M d0
  have hcard := two_K_le hw ho hK d0 hc I1
  -- domination of the sorted normalised values
  have hzo : Ord (fun S => w S / c) M := fun g hg h hh hgh =>
    div_le_div_of_nonneg_right (ho g hg h hh hgh) hc.le
  have hdom := sorted_dom (fun S => w S / c) u (normv w M f) M τ hτ huτ huo hzo
    (fun h _ => normv_le hw M f hc hf h)
  have hux : ∀ p < M.card, xs u M d0 p ≤ w {P p} / c := fun p hp => by
    rw [xs_of_lt hp]; exact hdom _ (ePos_mem hp)
  have hwc : ∀ a b : ℝ, a < 3 / 4 * c → a / c < 3 / 4 := fun a _ h => by
    rw [div_lt_iff₀ hc]; linarith
  have hanti := xs_anti hu huo d0
  have hx0 : xs u M d0 0 < 3 / 4 := lt_of_le_of_lt (hux 0 (by omega)) (hwc _ 0 I1)
  refine ⟨hK, hcard, hanti, xs_nonneg hu M d0, ?_, hx0, ?_, ?_, ?_⟩
  · -- the transported partition
    refine ⟨fun p => f (τ (P p)), fun q => ?_⟩
    have hT : M.filter (fun g => f (τ g) = q) ⊆ M := filter_subset _ _
    have e1 : (range M.card).filter (fun p => f (τ (P p)) = q) =
        (range M.card).filter (fun p => P p ∈ M.filter (fun g => f (τ g) = q)) := by
      ext p
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨hp, h⟩; exact ⟨hp, ePos_mem hp, h⟩
      · rintro ⟨hp, _, h⟩; exact ⟨hp, h⟩
    rw [e1, sum_xs_filter hu M d0 _ hT]
    have himg : (M.filter (fun g => f (τ g) = q)).image τ = M.filter (fun h => f h = q) := by
      ext h
      simp only [mem_image, mem_filter]
      constructor
      · rintro ⟨g, ⟨hgM, hgj⟩, rfl⟩
        exact ⟨hτ.mapsTo hgM, hgj⟩
      · rintro ⟨hhM, hhj⟩
        obtain ⟨g, hgM, rfl⟩ := hτ.surjOn hhM
        exact ⟨g, ⟨hgM, hhj⟩, rfl⟩
    rw [← normv_bundle hw M f hc hf q, ← himg, (normv_add1 hw M f).1 (Finset.image _ _),
      Finset.sum_image (fun x hx y hy h =>
        hτ.injOn (mem_filter.mp hx).1 (mem_filter.mp hy).1 h), hu.1]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    exact huτ g (mem_filter.mp hg).1
  · have h2 := I2 (by omega)
    have := hux (K - 1) (by omega)
    have := hux K (by omega)
    have : w {P (K - 1)} / c + w {P K} / c < 3 / 4 := by
      rw [← add_div]; exact hwc _ 0 h2
    linarith
  · intro p hp
    by_cases hpM : p < M.card
    · have h3 := I3 (by omega)
      have e1 := ord_pos ho d0 (a := 2 * K - 2) (b := 2 * K) (by omega) (by omega)
      have e2 := ord_pos ho d0 (a := 2 * K - 1) (b := 2 * K) (by omega) (by omega)
      have hlt : w {P (2 * K)} / c < 1 / 4 := by
        rw [div_lt_iff₀ hc]; simp only [P] at *; linarith
      have := hux (2 * K) (by omega)
      have := hanti hp
      linarith
    · rw [xs_of_ge (by omega)]; norm_num
  · intro p hp
    by_cases hpM : p < M.card
    · have h4 := I4 (by omega)
      have := hux 0 (by omega)
      have := hux (2 * K) (by omega)
      have := hanti hp
      have : w {P 0} / c + w {P (2 * K)} / c < 3 / 4 := by
        rw [← add_div]; exact hwc _ 0 h4
      linarith
    · rw [xs_of_ge (p := p) (by omega)]; linarith

end MMS34

-- ===== part C =====

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

namespace MMS34

open Finset

variable {n m : ℕ}

/-- The state invariant of bag filling, and its successful completion. -/
lemma bagfill_aux (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (c : ℕ)
    (B : ℕ → Finset (Fin m)) (L : Finset (Fin m))
    (hstuck : ∀ a ∈ N, ∀ C : ℕ → Finset (Fin m),
      (∀ k < c, ∀ k' < c, k ≠ k' → Disjoint (C k) (C k')) →
      (∀ g ∈ M, ∃ k < c, g ∈ C k) →
      (∀ k < c, B k ⊆ C k ∧ C k \ B k ⊆ L) →
      (∀ k < c, C k = B k ∨ ∃ g ∈ C k \ B k, v a ((C k).erase g) < 3 / 4) →
      (∃ k < c, v a (C k) < 3 / 4) → False) :
    ∀ (s : ℕ) (UA : Finset (Fin n)) (UB : Finset ℕ) (C : ℕ → Finset (Fin m))
      (G : Finset (Fin m)),
      UA.card + G.card = s → UA ⊆ N → UB ⊆ range c → UA.card = UB.card →
      (∀ k < c, B k ⊆ C k ∧ C k \ B k ⊆ L) →
      (∀ k < c, ∀ k' < c, k ≠ k' → Disjoint (C k) (C k')) →
      G ⊆ L → (∀ k < c, Disjoint (C k) G) →
      (∀ g ∈ M, g ∈ G ∨ ∃ k < c, g ∈ C k) →
      (∀ a ∈ UA, ∀ k < c, C k = B k ∨ ∃ g ∈ C k \ B k, v a ((C k).erase g) < 3 / 4) →
      ∃ C' : ℕ → Finset (Fin m), ∃ φ : Fin n → ℕ,
        (∀ k < c, k ∉ UB → C' k = C k) ∧ (∀ k < c, C' k ⊆ C k ∪ G) ∧
        (∀ k < c, ∀ k' < c, k ≠ k' → Disjoint (C' k) (C' k')) ∧
        (∀ a ∈ UA, φ a ∈ UB ∧ 3 / 4 ≤ v a (C' (φ a))) ∧ Set.InjOn φ UA := by
  classical
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro UA UB C G hs hUA hUB hcard hBC hdisj hGL hGdisj hcov hinv
  -- Case 1: nobody left
  by_cases hUAe : UA = ∅
  · subst hUAe
    refine ⟨C, fun _ => 0, fun _ _ _ => rfl, fun k _ => subset_union_left, hdisj, by simp,
      by simp⟩
  -- Case 2: someone values an open bag at ≥ 3/4
  by_cases hex : ∃ i ∈ UA, ∃ k ∈ UB, 3 / 4 ≤ v i (C k)
  · obtain ⟨i, hi, k, hk, hik⟩ := hex
    have hcardi : (UA.erase i).card + 1 = UA.card := card_erase_add_one hi
    obtain ⟨C', φ, h1, h2, h3, h4, h5⟩ := ih ((UA.erase i).card + G.card) (by omega)
      (UA.erase i) (UB.erase k) C G rfl ((erase_subset _ _).trans hUA)
      ((erase_subset _ _).trans hUB)
      (by rw [card_erase_of_mem hi, card_erase_of_mem hk, hcard]) hBC hdisj hGL hGdisj hcov
      (fun a ha => hinv a (mem_of_mem_erase ha))
    have hkc : k < c := mem_range.mp (hUB hk)
    refine ⟨C', Function.update φ i k, ?_, h2, h3, ?_, ?_⟩
    · intro k' hk' hk'UB
      exact h1 k' hk' (fun h => hk'UB (mem_of_mem_erase h))
    · intro a ha
      by_cases hai : a = i
      · subst hai
        rw [Function.update_self, h1 k hkc (by simp)]
        exact ⟨hk, hik⟩
      · rw [Function.update_of_ne hai]
        obtain ⟨hφ1, hφ2⟩ := h4 a (mem_erase.mpr ⟨hai, ha⟩)
        exact ⟨mem_of_mem_erase hφ1, hφ2⟩
    · intro a ha b hb hab
      have ha : a ∈ UA := ha
      have hb : b ∈ UA := hb
      by_cases hai : a = i <;> by_cases hbi : b = i
      · rw [hai, hbi]
      · exfalso
        rw [hai, Function.update_self, Function.update_of_ne hbi] at hab
        have := (h4 b (mem_erase.mpr ⟨hbi, hb⟩)).1
        rw [← hab] at this
        exact (notMem_erase k UB) this
      · exfalso
        rw [hbi, Function.update_self, Function.update_of_ne hai] at hab
        have := (h4 a (mem_erase.mpr ⟨hai, ha⟩)).1
        rw [hab] at this
        exact (notMem_erase k UB) this
      · rw [Function.update_of_ne hai, Function.update_of_ne hbi] at hab
        exact h5 (mem_erase.mpr ⟨hai, ha⟩) (mem_erase.mpr ⟨hbi, hb⟩) hab
  push_neg at hex
  obtain ⟨a0, ha0⟩ := nonempty_iff_ne_empty.mpr hUAe
  have hUBne : UB.Nonempty := by
    rw [← card_pos, ← hcard]; exact card_pos.mpr ⟨a0, ha0⟩
  obtain ⟨k, hk⟩ := hUBne
  have hkc : k < c := mem_range.mp (hUB hk)
  -- Case 4: out of goods: contradiction
  by_cases hGe : G = ∅
  · subst hGe
    exfalso
    refine hstuck a0 (hUA ha0) C hdisj ?_ hBC (hinv a0 ha0) ⟨k, hkc, hex a0 ha0 k hk⟩
    intro g hg
    rcases hcov g hg with h | h
    · simp at h
    · exact h
  -- Case 3: add a good to bag `k`
  obtain ⟨g, hg⟩ := nonempty_iff_ne_empty.mpr hGe
  have hgC : ∀ k' < c, g ∉ C k' := fun k' hk' h => disjoint_left.mp (hGdisj k' hk') h hg
  let C1 : ℕ → Finset (Fin m) := Function.update C k (insert g (C k))
  have hC1k : C1 k = insert g (C k) := Function.update_self _ _ _
  have hC1ne : ∀ k', k' ≠ k → C1 k' = C k' := fun k' h => Function.update_of_ne h _ _
  have hcardG : (G.erase g).card + 1 = G.card := card_erase_add_one hg
  have hBC1 : (∀ k' < c, B k' ⊆ C1 k' ∧ C1 k' \ B k' ⊆ L) := by
    intro k' hk'
    by_cases hne : k' = k
    · subst hne
      rw [hC1k]
      refine ⟨(hBC k' hk').1.trans (subset_insert _ _), ?_⟩
      intro x hx
      simp only [mem_sdiff, mem_insert] at hx
      rcases hx with ⟨rfl | hx, hxB⟩
      · exact hGL hg
      · exact (hBC k' hk').2 (mem_sdiff.mpr ⟨hx, hxB⟩)
    · rw [hC1ne k' hne]; exact hBC k' hk'
  have hdisj1 : (∀ k1 < c, ∀ k2 < c, k1 ≠ k2 → Disjoint (C1 k1) (C1 k2)) := by
    intro k1 hk1 k2 hk2 hne
    have key : ∀ k1 < c, ∀ k2 < c, k1 ≠ k2 → k1 = k → Disjoint (C1 k1) (C1 k2) := by
      intro k1 hk1 k2 hk2 hne h
      subst h
      rw [hC1k, hC1ne k2 (Ne.symm hne), disjoint_insert_left]
      exact ⟨hgC k2 hk2, hdisj k1 hk1 k2 hk2 hne⟩
    by_cases h1 : k1 = k
    · exact key k1 hk1 k2 hk2 hne h1
    by_cases h2 : k2 = k
    · exact (key k2 hk2 k1 hk1 (Ne.symm hne) h2).symm
    rw [hC1ne k1 h1, hC1ne k2 h2]
    exact hdisj k1 hk1 k2 hk2 hne
  have hGdisj1 : (∀ k' < c, Disjoint (C1 k') (G.erase g)) := by
    intro k' hk'
    by_cases hne : k' = k
    · subst hne
      rw [hC1k, disjoint_insert_left]
      refine ⟨by simp, ?_⟩
      exact disjoint_of_subset_right (erase_subset _ _) (hGdisj k' hk')
    · rw [hC1ne k' hne]
      exact disjoint_of_subset_right (erase_subset _ _) (hGdisj k' hk')
  have hcov1 : (∀ x ∈ M, x ∈ G.erase g ∨ ∃ k' < c, x ∈ C1 k') := by
    intro x hx
    rcases hcov x hx with h | ⟨k', hk', h⟩
    · by_cases hxg : x = g
      · subst hxg
        exact Or.inr ⟨k, hkc, by rw [hC1k]; exact mem_insert_self _ _⟩
      · exact Or.inl (mem_erase.mpr ⟨hxg, h⟩)
    · by_cases hne : k' = k
      · subst hne
        exact Or.inr ⟨k', hk', by rw [hC1k]; exact mem_insert_of_mem h⟩
      · exact Or.inr ⟨k', hk', by rw [hC1ne k' hne]; exact h⟩
  have hinv1 : (∀ a ∈ UA, ∀ k' < c, C1 k' = B k' ∨ ∃ g' ∈ C1 k' \ B k', v a ((C1 k').erase g') < 3 / 4) := by
    intro a ha k' hk'
    by_cases hne : k' = k
    · subst hne
      right
      refine ⟨g, ?_, ?_⟩
      · rw [hC1k]
        exact mem_sdiff.mpr ⟨mem_insert_self _ _, fun h => hgC k' hk' ((hBC k' hk').1 h)⟩
      · rw [hC1k, erase_insert (hgC k' hk')]
        exact hex a ha k' hk
    · rw [hC1ne k' hne]; exact hinv a ha k' hk'


  obtain ⟨C', φ, h1, h2, h3, h4, h5⟩ := ih (UA.card + (G.erase g).card) (by omega)
    UA UB C1 (G.erase g) rfl hUA hUB hcard hBC1 hdisj1 ((erase_subset _ _).trans hGL) hGdisj1 hcov1 hinv1
  refine ⟨C', φ, ?_, ?_, h3, h4, h5⟩
  · intro k' hk' hk'UB
    have hne : k' ≠ k := fun h => hk'UB (h ▸ hk)
    rw [h1 k' hk' hk'UB, hC1ne k' hne]
  · intro k' hk'
    refine (h2 k' hk').trans ?_
    by_cases hne : k' = k
    · subst hne
      rw [hC1k]
      intro x hx
      simp only [mem_union, mem_insert, mem_erase] at hx ⊢
      rcases hx with (rfl | hx) | ⟨_, hx⟩
      · exact Or.inr hg
      · exact Or.inl hx
      · exact Or.inr hx
    · rw [hC1ne k' hne]
      exact union_subset_union le_rfl (erase_subset _ _)
theorem bagfill (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (hN : N.Nonempty) (M : Finset (Fin m)) (c : ℕ) (hc : N.card = c)
    (B : ℕ → Finset (Fin m)) (L : Finset (Fin m))
    (hBM : ∀ k < c, B k ⊆ M) (hBdisj : ∀ k < c, ∀ k' < c, k ≠ k' → Disjoint (B k) (B k'))
    (hL : L ⊆ M) (hLdisj : ∀ k < c, Disjoint (B k) L)
    (hcover : ∀ g ∈ M, g ∈ L ∨ ∃ k < c, g ∈ B k)
    (hstuck : ∀ a ∈ N, ∀ C : ℕ → Finset (Fin m),
      (∀ k < c, ∀ k' < c, k ≠ k' → Disjoint (C k) (C k')) →
      (∀ g ∈ M, ∃ k < c, g ∈ C k) →
      (∀ k < c, B k ⊆ C k ∧ C k \ B k ⊆ L) →
      (∀ k < c, C k = B k ∨ ∃ g ∈ C k \ B k, v a ((C k).erase g) < 3 / 4) →
      (∃ k < c, v a (C k) < 3 / 4) → False) :
    ∃ A : Fin m → Fin n, (∀ b ∈ M, A b ∈ N) ∧
      ∀ i ∈ N, 3 / 4 ≤ v i (M.filter (fun b => A b = i)) := by
  classical
  obtain ⟨C', φ, _, h2, h3, h4, h5⟩ := bagfill_aux v hv N M c B L hstuck _ N (range c) B L rfl
    le_rfl le_rfl (by rw [card_range, hc]) (fun k _ => ⟨le_rfl, by simp⟩) hBdisj le_rfl hLdisj
    hcover (fun a _ k _ => Or.inl rfl)
  obtain ⟨a0, ha0⟩ := hN
  let A : Fin m → Fin n := fun g => if h : ∃ a ∈ N, g ∈ C' (φ a) then Classical.choose h else a0
  refine ⟨A, ?_, ?_⟩
  · intro b _
    simp only [A]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact ha0
  · intro i hi
    refine le_trans (h4 i hi).2 ((add1_of hv i).mono ?_)
    intro g hg
    have hφi := mem_range.mp (h4 i hi).1
    refine mem_filter.mpr ⟨?_, ?_⟩
    · have := h2 _ hφi hg
      rcases mem_union.mp this with h | h
      · exact hBM _ hφi h
      · exact hL h
    · have hex : ∃ a ∈ N, g ∈ C' (φ a) := ⟨i, hi, hg⟩
      simp only [A, dif_pos hex]
      obtain ⟨ha, hga⟩ := Classical.choose_spec hex
      set a := Classical.choose hex
      have hφa := mem_range.mp (h4 a ha).1
      by_contra hne
      have hφne : φ a ≠ φ i := fun h => hne (h5 ha hi h)
      exact disjoint_left.mp (h3 _ hφa _ hφi hφne) hga hg

end MMS34

-- ===== part F =====

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

namespace MMS34

open Finset

variable {n m : ℕ}

/-- The ONI stage: an ordered, totally-3/4-irreducible instance with positive MMS values
admits a 3/4-MMS allocation (normalise, re-sort, bag-fill, transfer back). -/
theorem oni_stage (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (hN : N.Nonempty) (M : Finset (Fin m)) (d0 : Fin m)
    (hord : ∀ i, Ord (v i) M) (hpos : ∀ i ∈ N, 0 < mms (v i) N.card M)
    (I1 : ∀ i ∈ N, v i {ePos M d0 0} < 3 / 4 * mms (v i) N.card M)
    (I2 : ∀ i ∈ N, N.card + 1 ≤ M.card →
      v i {ePos M d0 (N.card - 1)} + v i {ePos M d0 N.card} < 3 / 4 * mms (v i) N.card M)
    (I3 : ∀ i ∈ N, 2 * N.card + 1 ≤ M.card →
      v i {ePos M d0 (2 * N.card - 2)} + v i {ePos M d0 (2 * N.card - 1)} +
        v i {ePos M d0 (2 * N.card)} < 3 / 4 * mms (v i) N.card M)
    (I4 : ∀ i ∈ N, 2 * N.card + 1 ≤ M.card →
      v i {ePos M d0 0} + v i {ePos M d0 (2 * N.card)} < 3 / 4 * mms (v i) N.card M) :
    AdmitsMMSAlloc (3 / 4) v N M := by
  classical
  set K := N.card with hKdef
  have hK : 0 < K := card_pos.mpr hN
  set P := ePos M d0 with hP
  -- MMS labellings
  have hlab : ∀ i, ∃ f : Fin m → Fin K, ∀ j, mms (v i) K M ≤ v i (M.filter (fun g => f g = j)) :=
    fun i => mms_attained (v i) hK M
  choose f hf using hlab
  -- normalised valuations
  let wh : Fin n → Finset (Fin m) → ℝ := fun i => if i ∈ N then normv (v i) M (f i) else v i
  have hwh : ∀ i, Add1 (wh i) := by
    intro i
    by_cases hi : i ∈ N
    · simp only [wh, if_pos hi]; exact normv_add1 (add1_of hv i) M (f i)
    · simp only [wh, if_neg hi]; exact add1_of hv i
  -- sorted versions
  have hsort : ∀ i, ∃ τ : Fin m → Fin m, Set.BijOn τ M M ∧
      ∀ g ∈ M, ∀ h ∈ M, g ≤ h → wh i {τ h} ≤ wh i {τ g} := fun i => exists_sort (wh i) M
  choose τ hτ hτo using hsort
  let u : Fin n → Finset (Fin m) → ℝ := fun i S => ∑ g ∈ S, wh i {τ i g}
  have hus : ∀ i g, u i {g} = wh i {τ i g} := fun i g => by simp [u]
  have hu : IsAdditive u := by
    refine ⟨fun i S => ?_, fun i S => ?_⟩
    · simp only [hus]; rfl
    · exact Finset.sum_nonneg (fun g _ => (hwh i).2 _)
  have huo : ∀ i, Ord (u i) M := by
    intro i g hg h hh hgh
    rw [hus, hus]; exact hτo i g hg h hh hgh
  have hwhv : IsAdditive wh := ⟨fun i => (hwh i).1, fun i => (hwh i).2⟩
  -- per-agent ONI
  have hONI : ∀ a ∈ N, ONI K M.card (xs (u a) M d0) := by
    intro a ha
    refine agent_ONI (add1_of hv a) (hord a) hK d0 (hpos a ha) (I1 a ha) (I2 a ha) (I3 a ha)
      (I4 a ha) (f a) (hf a) (τ a) (hτ a) (u a) (add1_of hu a) (fun g _ => ?_) (huo a)
    rw [hus]; simp only [wh, if_pos ha]
  -- 2K ≤ |M|
  obtain ⟨a0, ha0⟩ := hN
  have hcard : 2 * K ≤ M.card := (hONI a0 ha0).card
  have hPinj : ∀ x y, x < M.card → y < M.card → (P x = P y ↔ x = y) :=
    fun x y hx hy => ePos_inj hx hy
  have hPmem : ∀ x, x < M.card → P x ∈ M := fun x hx => ePos_mem hx
  -- bags
  let B : ℕ → Finset (Fin m) := fun k => {P k, P (2 * K - 1 - k)}
  let L : Finset (Fin m) := (Ico (2 * K) M.card).image P
  have hmemB : ∀ k < K, ∀ g, g ∈ B k ↔ g = P k ∨ g = P (2 * K - 1 - k) := by
    intro k _ g; simp [B]
  have hmemL : ∀ g, g ∈ L ↔ ∃ p, 2 * K ≤ p ∧ p < M.card ∧ P p = g := by
    intro g; simp [L, and_assoc]
  have hBM : ∀ k < K, B k ⊆ M := by
    intro k hk g hg
    rcases (hmemB k hk g).mp hg with rfl | rfl
    · exact hPmem _ (by omega)
    · exact hPmem _ (by omega)
  have hBdisj : ∀ k < K, ∀ k' < K, k ≠ k' → Disjoint (B k) (B k') := by
    intro k hk k' hk' hne
    rw [Finset.disjoint_left]
    intro g hg hg'
    rcases (hmemB k hk g).mp hg with rfl | rfl <;>
      rcases (hmemB k' hk' _).mp hg' with h | h <;>
      · rw [hPinj _ _ (by omega) (by omega)] at h; omega
  have hL : L ⊆ M := by
    intro g hg
    obtain ⟨p, _, hp, rfl⟩ := (hmemL g).mp hg
    exact hPmem p hp
  have hLdisj : ∀ k < K, Disjoint (B k) L := by
    intro k hk
    rw [Finset.disjoint_left]
    intro g hg hgL
    obtain ⟨p, hp1, hp2, rfl⟩ := (hmemL g).mp hgL
    rcases (hmemB k hk _).mp hg with h | h <;>
    · rw [hPinj _ _ (by omega) (by omega)] at h; omega
  have hcover : ∀ g ∈ M, g ∈ L ∨ ∃ k < K, g ∈ B k := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := ePos_surj (d := d0) hg
    by_cases h1 : 2 * K ≤ p
    · exact Or.inl ((hmemL _).mpr ⟨p, h1, hp, rfl⟩)
    by_cases h2 : p < K
    · exact Or.inr ⟨p, h2, (hmemB p h2 _).mpr (Or.inl rfl)⟩
    · refine Or.inr ⟨2 * K - 1 - p, by omega, (hmemB _ (by omega) _).mpr (Or.inr ?_)⟩
      congr 1; omega
  -- the no-stuck property for each agent
  have hstuck : ∀ a ∈ N, ∀ C : ℕ → Finset (Fin m),
      (∀ k < K, ∀ k' < K, k ≠ k' → Disjoint (C k) (C k')) →
      (∀ g ∈ M, ∃ k < K, g ∈ C k) →
      (∀ k < K, B k ⊆ C k ∧ C k \ B k ⊆ L) →
      (∀ k < K, C k = B k ∨ ∃ g ∈ C k \ B k, u a ((C k).erase g) < 3 / 4) →
      (∃ k < K, u a (C k) < 3 / 4) → False := by
    intro a ha C hCdisj hCcov hBC hinv hlt
    have hx := hONI a ha
    have hua := add1_of hu a
    have hCM : ∀ k < K, C k ⊆ M := by
      intro k hk g hg
      by_cases hgB : g ∈ B k
      · exact hBM k hk hgB
      · exact hL ((hBC k hk).2 (mem_sdiff.mpr ⟨hg, hgB⟩))
    let C' : ℕ → Finset ℕ := fun k => (range M.card).filter (fun p => P p ∈ C k)
    have hmemC' : ∀ k p, p ∈ C' k ↔ p < M.card ∧ P p ∈ C k := by
      intro k p; simp [C']
    have hsumC' : ∀ k < K, ∑ p ∈ C' k, xs (u a) M d0 p = u a (C k) :=
      fun k hk => sum_xs_filter hua M d0 (C k) (hCM k hk)
    refine no_stuck hx C' ?_ ?_ ?_ ?_ ?_
    · -- total
      have hall : (range M.card).filter (fun p => P p ∈ M) = range M.card :=
        Finset.filter_true_of_mem (fun p hp => hPmem p (mem_range.mp hp))
      rw [← hall, sum_xs_filter hua M d0 M le_rfl,
        Finset.sum_congr rfl (fun k hk => hsumC' k (mem_range.mp hk))]
      have hU : M = (range K).biUnion C := by
        ext g
        simp only [mem_biUnion, mem_range]
        constructor
        · intro hg; exact hCcov g hg
        · rintro ⟨k, hk, hg⟩; exact hCM k hk hg
      rw [hU, hua.1, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← hua.1]
      · intro k hk k' hk' hne
        exact hCdisj k (mem_range.mp hk) k' (mem_range.mp hk') hne
    · intro k hk
      refine ⟨(hmemC' k k).mpr ⟨by omega, (hBC k hk).1 ((hmemB k hk _).mpr (Or.inl rfl))⟩,
        (hmemC' k _).mpr ⟨by omega, (hBC k hk).1 ((hmemB k hk _).mpr (Or.inr rfl))⟩⟩
    · intro k hk p hp hpk hpk'
      obtain ⟨hpM, hpC⟩ := (hmemC' k p).mp hp
      by_cases hpB : P p ∈ B k
      · exfalso
        rcases (hmemB k hk _).mp hpB with h | h
        · rw [hPinj _ _ hpM (by omega)] at h; exact hpk h
        · rw [hPinj _ _ hpM (by omega)] at h; exact hpk' h
      · obtain ⟨p', hp'1, hp'2, he⟩ := (hmemL _).mp ((hBC k hk).2 (mem_sdiff.mpr ⟨hpC, hpB⟩))
        rw [hPinj _ _ hp'2 hpM] at he
        omega
    · intro k hk
      rcases hinv k hk with h | ⟨g, hg, hglt⟩
      · left
        ext p
        rw [hmemC', h]
        simp only [mem_insert, mem_singleton]
        constructor
        · rintro ⟨hpM, hpB⟩
          rcases (hmemB k hk _).mp hpB with e | e
          · exact Or.inl ((hPinj _ _ hpM (by omega)).mp e)
          · exact Or.inr ((hPinj _ _ hpM (by omega)).mp e)
        · rintro (rfl | rfl)
          · exact ⟨by omega, (hmemB p hk _).mpr (Or.inl rfl)⟩
          · exact ⟨by omega, (hmemB k hk _).mpr (Or.inr rfl)⟩
      · right
        obtain ⟨hgC, hgB⟩ := mem_sdiff.mp hg
        obtain ⟨p0, hp01, hp02, rfl⟩ := (hmemL _).mp ((hBC k hk).2 hg)
        refine ⟨p0, (hmemC' k p0).mpr ⟨hp02, hgC⟩, by omega, by omega, ?_⟩
        have he : (C' k).erase p0 =
            (range M.card).filter (fun p => P p ∈ (C k).erase (P p0)) := by
          ext p
          simp only [mem_erase, hmemC', mem_filter, mem_range]
          constructor
          · rintro ⟨hne, hpM, hpC⟩
            exact ⟨hpM, fun e => hne ((hPinj _ _ hpM hp02).mp e), hpC⟩
          · rintro ⟨hpM, hne, hpC⟩
            exact ⟨fun e => hne (e ▸ rfl), hpM, hpC⟩
        rw [he, sum_xs_filter hua M d0 _ ((erase_subset _ _).trans (hCM k hk))]
        exact hglt
    · obtain ⟨k, hk, hkl⟩ := hlt
      exact ⟨k, hk, by rw [hsumC' k hk]; exact hkl⟩
  -- run bag filling on the instance `u`
  obtain ⟨A', hA'N, hA'v⟩ := bagfill u hu N ⟨a0, ha0⟩ M K rfl B L hBM hBdisj hL hLdisj
    hcover hstuck
  -- transfer back to `wh` by picking
  obtain ⟨A, hAN, hAv⟩ := picking wh u hwhv hu M τ hτ (fun i g _ => hus i g) huo A'
  refine ⟨A, ?_, ?_⟩
  · intro b hb
    obtain ⟨g, hg, e⟩ := hAN b hb
    rw [e]; exact hA'N g hg
  · intro i hi
    have h1 := hA'v i hi
    have h2 := hAv i
    have h3 := normv_mul_le (add1_of hv i) M (f i) (hpos i hi) (hf i)
      (M.filter (fun b => A b = i))
    have h4 : wh i (M.filter (fun b => A b = i)) = normv (v i) M (f i)
        (M.filter (fun b => A b = i)) := by simp only [wh, if_pos hi]
    have h5 := hpos i hi
    rw [h4] at h2
    nlinarith

end MMS34

-- ===== part G =====

set_option autoImplicit false
open LittleCharity.MMS ImprovedMMS.Additive

namespace MMS34

open Finset

variable {n m : ℕ}

/-- A valid reduction preserves the existence of a 3/4-MMS allocation. -/
lemma admits_of_red (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (i : Fin n) (hi : i ∈ N) (S : Finset (Fin m))
    (hS : S ⊆ M) (hiS : 3 / 4 * mms (v i) N.card M ≤ v i S)
    (hval : ∀ j ∈ N, j ≠ i → mms (v j) N.card M ≤ mms (v j) (N.card - 1) (M \ S))
    (hrec : AdmitsMMSAlloc (3 / 4) v (N.erase i) (M \ S)) :
    AdmitsMMSAlloc (3 / 4) v N M := by
  classical
  obtain ⟨A', hA'N, hA'v⟩ := hrec
  refine ⟨fun g => if g ∈ S then i else A' g, ?_, ?_⟩
  · intro b hb
    by_cases hbS : b ∈ S
    · simp only [if_pos hbS]; exact hi
    · simp only [if_neg hbS]
      exact mem_of_mem_erase (hA'N b (mem_sdiff.mpr ⟨hb, hbS⟩))
  · intro j hj
    by_cases hji : j = i
    · subst hji
      refine hiS.trans ((add1_of hv j).mono ?_)
      intro g hg
      exact mem_filter.mpr ⟨hS hg, by simp [hg]⟩
    · have h1 := hA'v j (mem_erase.mpr ⟨hji, hj⟩)
      rw [card_erase_of_mem hi] at h1
      have h2 := hval j hj hji
      refine le_trans ?_ (h1.trans ((add1_of hv j).mono ?_))
      · linarith
      · intro g hg
        simp only [mem_filter, mem_sdiff] at hg
        refine mem_filter.mpr ⟨hg.1.1, ?_⟩
        simp only [if_neg hg.1.2]; exact hg.2

/-- Transfer through sorting (toOrd). -/
lemma admits_of_sorted (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (τ : Fin n → Fin m → Fin m)
    (hτ : ∀ i, Set.BijOn (τ i) M M) (z : Fin n → Finset (Fin m) → ℝ) (hz : IsAdditive z)
    (hzv : ∀ i, ∀ g ∈ M, z i {g} = v i {τ i g}) (hzo : ∀ i, Ord (z i) M)
    (h : AdmitsMMSAlloc (3 / 4) z N M) : AdmitsMMSAlloc (3 / 4) v N M := by
  classical
  obtain ⟨A', hA'N, hA'v⟩ := h
  obtain ⟨A, hAN, hAv⟩ := picking v z hv hz M τ hτ hzv hzo A'
  refine ⟨A, ?_, ?_⟩
  · intro b hb
    obtain ⟨g, hg, e⟩ := hAN b hb
    rw [e]; exact hA'N g hg
  · intro i hi
    by_cases hN : N.card = 0
    · rw [hN]
      have : mms (v i) 0 M = 0 := by
        unfold mms
        simp
      rw [this, mul_zero]; exact (hv.2 i _)
    have hle := mms_le_of_bij (add1_of hv i) (add1_of hz i) (Nat.pos_of_ne_zero hN) M (τ i)
      (hτ i) (hzv i)
    have := hA'v i hi
    have := hAv i
    linarith

/-- The main induction. -/
theorem main_ind : ∀ t : ℕ, ∀ (v : Fin n → Finset (Fin m) → ℝ), IsAdditive v →
    ∀ (N : Finset (Fin n)) (M : Finset (Fin m)), N.card = t + 1 →
      AdmitsMMSAlloc (3 / 4) v N M := by
  classical
  intro t
  induction t with
  | zero =>
    intro v hv N M hN
    obtain ⟨i, rfl⟩ := card_eq_one.mp hN
    refine ⟨fun _ => i, fun _ _ => mem_singleton_self i, ?_⟩
    intro j hj
    rw [mem_singleton] at hj
    subst hj
    have h1 := mms_mul_le (add1_of hv j) (k := 1) Nat.one_pos M
    have h0 := mms_nonneg (add1_of hv j) (k := 1) Nat.one_pos M
    rw [card_singleton, Finset.filter_true_of_mem (fun _ _ => rfl)]
    simp only [Nat.cast_one, one_mul] at h1
    linarith
  | succ k ih =>
    intro v0 hv0 N M hN
    -- sort
    have hsort : ∀ i, ∃ τ : Fin m → Fin m, Set.BijOn τ M M ∧
        ∀ g ∈ M, ∀ h ∈ M, g ≤ h → v0 i {τ h} ≤ v0 i {τ g} := fun i => exists_sort (v0 i) M
    choose τ hτ hτo using hsort
    let v : Fin n → Finset (Fin m) → ℝ := fun i S => ∑ g ∈ S, v0 i {τ i g}
    have hvs : ∀ i g, v i {g} = v0 i {τ i g} := fun i g => by simp [v]
    have hv : IsAdditive v := by
      refine ⟨fun i S => ?_, fun i S => ?_⟩
      · simp only [hvs]; rfl
      · exact Finset.sum_nonneg (fun g _ => hv0.2 i _)
    have hord : ∀ i, Ord (v i) M := by
      intro i g hg h hh hgh
      rw [hvs, hvs]; exact hτo i g hg h hh hgh
    refine admits_of_sorted v0 hv0 N M τ hτ v hv (fun i g _ => hvs i g) hord ?_
    -- reductions
    have hK : N.card = k + 2 := hN
    have hrec : ∀ i ∈ N, ∀ S : Finset (Fin m), AdmitsMMSAlloc (3 / 4) v (N.erase i) (M \ S) :=
      fun i hi S => ih v hv (N.erase i) (M \ S) (by rw [card_erase_of_mem hi, hK]; omega)
    have hsub1 : N.card - 1 = k + 1 := by omega
    -- (c0) an agent with zero MMS
    by_cases c0 : ∃ i ∈ N, mms (v i) N.card M ≤ 0
    · obtain ⟨i, hi, hle⟩ := c0
      refine admits_of_red v hv N M i hi ∅ (empty_subset _) ?_ ?_ (hrec i hi ∅)
      · rw [(add1_of hv i).empty]; linarith
      · intro j _ _
        rw [hsub1, hK]; exact valid_empty (add1_of hv j) M
    push_neg at c0
    -- M is non-empty
    obtain ⟨i0, hi0⟩ : N.Nonempty := card_pos.mp (by omega)
    have hMne : M.Nonempty := by
      by_contra hM
      rw [not_nonempty_iff_eq_empty] at hM
      have h1 := mms_mul_le (add1_of hv i0) (card_pos.mpr ⟨i0, hi0⟩) M
      rw [hM, (add1_of hv i0).empty] at h1
      have h2 := c0 i0 hi0
      rw [hM] at h2
      have : (0 : ℝ) < N.card := by exact_mod_cast card_pos.mpr ⟨i0, hi0⟩
      nlinarith
    obtain ⟨d0, hd0⟩ := hMne
    set P := ePos M d0 with hP
    have hPmem : ∀ x, x < M.card → P x ∈ M := fun x hx => ePos_mem hx
    have hPinj : ∀ x y, x < M.card → y < M.card → x ≠ y → P x ≠ P y :=
      fun x y hx hy h e => h ((ePos_inj hx hy).mp e)
    have hM1 : 1 ≤ M.card := card_pos.mpr ⟨d0, hd0⟩
    -- (c1)
    by_cases c1 : ∃ i ∈ N, 3 / 4 * mms (v i) N.card M ≤ v i {P 0}
    · obtain ⟨i, hi, hle⟩ := c1
      refine admits_of_red v hv N M i hi {P 0} (by simpa using hPmem 0 (by omega)) hle ?_
        (hrec i hi _)
      intro j _ _
      rw [hsub1, hK]; exact valid_one (add1_of hv j) M _
    push_neg at c1
    -- (c2)
    by_cases c2 : N.card + 1 ≤ M.card ∧
        ∃ i ∈ N, 3 / 4 * mms (v i) N.card M ≤ v i {P (N.card - 1), P N.card}
    · obtain ⟨hMc, i, hi, hle⟩ := c2
      have hsub : ({P (N.card - 1), P N.card} : Finset (Fin m)) ⊆ M := by
        intro g hg
        simp only [mem_insert, mem_singleton] at hg
        rcases hg with rfl | rfl
        · exact hPmem _ (by omega)
        · exact hPmem _ (by omega)
      refine admits_of_red v hv N M i hi _ hsub hle ?_ (hrec i hi _)
      intro j _ _
      have := valid_two (add1_of hv j) (hord j) (k := k) d0 (by omega)
      rw [hsub1, hK]
      exact this
    have c2' : ∀ i ∈ N, N.card + 1 ≤ M.card →
        v i {P (N.card - 1)} + v i {P N.card} < 3 / 4 * mms (v i) N.card M := by
      intro i hi hMc
      have : ¬ 3 / 4 * mms (v i) N.card M ≤ v i {P (N.card - 1), P N.card} :=
        fun h => c2 ⟨hMc, i, hi, h⟩
      push_neg at this
      rwa [(add1_of hv i).pair (hPinj _ _ (by omega) (by omega) (by omega))] at this
    -- (c3)
    by_cases c3 : 2 * N.card + 1 ≤ M.card ∧ ∃ i ∈ N, 3 / 4 * mms (v i) N.card M ≤
        v i {P (2 * N.card - 2), P (2 * N.card - 1), P (2 * N.card)}
    · obtain ⟨hMc, i, hi, hle⟩ := c3
      have hsub : ({P (2 * N.card - 2), P (2 * N.card - 1), P (2 * N.card)} :
          Finset (Fin m)) ⊆ M := by
        intro g hg
        simp only [mem_insert, mem_singleton] at hg
        rcases hg with rfl | rfl | rfl
        · exact hPmem _ (by omega)
        · exact hPmem _ (by omega)
        · exact hPmem _ (by omega)
      refine admits_of_red v hv N M i hi _ hsub hle ?_ (hrec i hi _)
      intro j _ _
      have := valid_three (add1_of hv j) (hord j) (k := k) d0 (by omega)
      rw [hsub1, hK]
      exact this
    have triple : ∀ i, 2 * N.card + 1 ≤ M.card →
        v i {P (2 * N.card - 2), P (2 * N.card - 1), P (2 * N.card)} =
          v i {P (2 * N.card - 2)} + v i {P (2 * N.card - 1)} + v i {P (2 * N.card)} := by
      intro i hMc
      rw [(add1_of hv i).insert (by
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hPinj _ _ (by omega) (by omega) (by omega),
          hPinj _ _ (by omega) (by omega) (by omega)⟩),
        (add1_of hv i).pair (hPinj _ _ (by omega) (by omega) (by omega))]
      ring
    have c3' : ∀ i ∈ N, 2 * N.card + 1 ≤ M.card →
        v i {P (2 * N.card - 2)} + v i {P (2 * N.card - 1)} + v i {P (2 * N.card)} <
          3 / 4 * mms (v i) N.card M := by
      intro i hi hMc
      have : ¬ 3 / 4 * mms (v i) N.card M ≤
          v i {P (2 * N.card - 2), P (2 * N.card - 1), P (2 * N.card)} :=
        fun h => c3 ⟨hMc, i, hi, h⟩
      push_neg at this
      rwa [triple i hMc] at this
    -- (c4)
    by_cases c4 : 2 * N.card + 1 ≤ M.card ∧
        ∃ i ∈ N, 3 / 4 * mms (v i) N.card M ≤ v i {P 0, P (2 * N.card)}
    · obtain ⟨hMc, i, hi, hle⟩ := c4
      have hsub : ({P 0, P (2 * N.card)} : Finset (Fin m)) ⊆ M := by
        intro g hg
        simp only [mem_insert, mem_singleton] at hg
        rcases hg with rfl | rfl
        · exact hPmem _ (by omega)
        · exact hPmem _ (by omega)
      refine admits_of_red v hv N M i hi _ hsub hle ?_ (hrec i hi _)
      intro j hj _
      have h1 := c1 j hj
      have h3 := c3' j hj hMc
      have e1 := ord_pos (hord j) d0 (a := 2 * N.card - 2) (b := 2 * N.card) (by omega) (by omega)
      have e2 := ord_pos (hord j) d0 (a := 2 * N.card - 1) (b := 2 * N.card) (by omega) (by omega)
      have hpos := c0 j hj
      rw [hsub1]
      rw [hK] at h1 h3 e1 e2 hpos ⊢
      refine valid_four (add1_of hv j) M (hPmem _ (by omega)) (hPmem _ (by omega))
        (hPinj _ _ (by omega) (by omega) (by omega)) ?_
      simp only [P] at *
      linarith
    have c4' : ∀ i ∈ N, 2 * N.card + 1 ≤ M.card →
        v i {P 0} + v i {P (2 * N.card)} < 3 / 4 * mms (v i) N.card M := by
      intro i hi hMc
      have : ¬ 3 / 4 * mms (v i) N.card M ≤ v i {P 0, P (2 * N.card)} :=
        fun h => c4 ⟨hMc, i, hi, h⟩
      push_neg at this
      rwa [(add1_of hv i).pair (hPinj _ _ (by omega) (by omega) (by omega))] at this
    -- totally irreducible: the ONI stage
    exact oni_stage v hv N ⟨i0, hi0⟩ M d0 hord c0 c1 c2' c3' c4'

end MMS34

open MMS34 in
theorem final_3_39 {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : IsAdditive v) :
    ∃ A : Fin m → Fin n, ∀ i : Fin n,
      (3 / 4 : ℝ) * mms (v i) n Finset.univ ≤ v i (Finset.univ.filter (fun b => A b = i)) := by
  obtain ⟨A, _, hA⟩ := main_ind (n - 1) v hv Finset.univ Finset.univ
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  refine ⟨A, fun i => ?_⟩
  have := hA i (Finset.mem_univ i)
  rwa [Finset.card_univ, Fintype.card_fin] at this


theorem solution {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : IsAdditive v) :
    ∃ A : Fin m → Fin n, ∀ i : Fin n,
      (3 / 4 : ℝ) * mms (v i) n Finset.univ ≤ v i (Finset.univ.filter (fun b => A b = i)) :=
  final_3_39 hn v hv
