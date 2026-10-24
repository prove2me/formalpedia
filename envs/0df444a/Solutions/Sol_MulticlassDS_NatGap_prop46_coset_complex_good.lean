-- Prove2me | solution 1 for MulticlassDS.NatGap.prop46_coset_complex_good
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T21:56:45.450979+00:00
-- url     : https://prove2.me/submissions/18ceb2cf-9b44-461d-a9a6-28f96175d6c7

import Init
import Definitions.Def_MulticlassDS_NatGap_Complexes

open Classical Pointwise
namespace CosetGood
open MulticlassDS.NatGap
variable {F : Type*} [Group F] {d : ℕ} (Hs : Fin d → Subgroup F)

lemma anchor (H : Subgroup F) {a x : F} (hx : x ∈ a • (H : Set F)) :
    a • (H : Set F) = x • (H : Set F) := by
  rcases hx with ⟨h, hh, rfl⟩
  ext y
  change (∃ k, k ∈ H ∧ a * k = y) ↔ (∃ k, k ∈ H ∧ (a * h) * k = y)
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨h⁻¹ * k, H.mul_mem (H.inv_mem hh) hk, by simp [mul_assoc]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨h * k, H.mul_mem hh hk, by simp [mul_assoc]⟩

lemma center_mem (H : Subgroup F) (g : F) : g ∈ g • (H : Set F) :=
  ⟨1, H.one_mem, by simp⟩

lemma cancel_cosets (H K : Subgroup F) (g : F)
    (he : g • (H : Set F) = g • (K : Set F)) : H = K := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    have hm : g * x ∈ g • (K : Set F) := he ▸ ⟨x, hx, rfl⟩
    rcases hm with ⟨y, hy, heq⟩
    exact mul_left_cancel heq ▸ hy
  · intro hx
    have hm : g * x ∈ g • (H : Set F) := he.symm ▸ ⟨x, hx, rfl⟩
    rcases hm with ⟨y, hy, heq⟩
    exact mul_left_cancel heq ▸ hy

variable (h1 : ∀ i : Fin d, ∃ z : F, (∀ j : Fin d, j ≠ i → z ∈ Hs j) ∧ z ∉ Hs i)

include h1 in
lemma subgroup_injective : Function.Injective Hs := by
  intro i j he
  by_contra hn
  obtain ⟨z, hz, hnz⟩ := h1 i
  apply hnz
  rw [he]
  exact hz j (Ne.symm hn)

include h1 in
lemma index_unique (a b : F) (i j : Fin d)
    (he : a • (Hs i : Set F) = b • (Hs j : Set F)) : i = j := by
  have ha : a ∈ b • (Hs j : Set F) := he ▸ center_mem (Hs i) a
  have hb := anchor (Hs j) ha
  apply subgroup_injective Hs h1
  exact cancel_cosets (Hs i) (Hs j) a (he.trans hb)

noncomputable def chamber (g : F) : Finset (Set F) :=
  Finset.univ.image (fun i => g • (Hs i : Set F))

lemma face_iff (f : Finset (Set F)) :
    f ∈ cosetComplex Hs ↔ ∃ g : F, f ⊆ chamber Hs g := by
  classical
  constructor
  · rintro ⟨hf, g, hg⟩
    refine ⟨g, ?_⟩
    intro L hL
    obtain ⟨i, a, ha⟩ := hf L hL
    have hgL : g ∈ L := Set.mem_iInter.mp (Set.mem_iInter.mp hg L) hL
    have he : L = g • (Hs i : Set F) := ha.trans (anchor (Hs i) (ha ▸ hgL))
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩
  · rintro ⟨g, hf⟩
    constructor
    · intro L hL
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hf hL)
      exact ⟨i, g, rfl⟩
    · refine ⟨g, Set.mem_iInter.mpr (fun L => Set.mem_iInter.mpr (fun hL => ?_))⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hf hL)
      exact center_mem (Hs i) g

lemma chamber_face (g : F) : chamber Hs g ∈ cosetComplex Hs :=
  (face_iff Hs _).2 ⟨g, Finset.Subset.refl _⟩

include h1 in
lemma chamber_card (g : F) : (chamber Hs g).card = d := by
  classical
  rw [chamber, Finset.card_image_of_injective]
  · simp
  · intro i j he
    exact index_unique Hs h1 g g i j he

end CosetGood

open Classical Pointwise
namespace CosetGood
open MulticlassDS.NatGap
variable {F : Type*} [Group F] {d : ℕ} (Hs : Fin d → Subgroup F)
variable (h1 : ∀ i : Fin d, ∃ z : F, (∀ j : Fin d, j ≠ i → z ∈ Hs j) ∧ z ∉ Hs i)

noncomputable def color (hd : 0 < d) (L : Set F) : Fin d :=
  if h : IsCosetVertex Hs L then h.choose else ⟨0, hd⟩

include h1 in
lemma color_coset (hd : 0 < d) (g : F) (i : Fin d) :
    color Hs hd (g • (Hs i : Set F)) = i := by
  have hv : IsCosetVertex Hs (g • (Hs i : Set F)) := ⟨i, g, rfl⟩
  simp only [color, dif_pos hv]
  obtain ⟨a, ha⟩ := hv.choose_spec
  exact index_unique Hs h1 a g hv.choose i ha.symm

lemma complex : IsComplex (cosetComplex Hs) := by
  intro f hf q hq
  obtain ⟨g, hg⟩ := (face_iff Hs f).1 hf
  exact (face_iff Hs q).2 ⟨g, hq.trans hg⟩

include h1 in
lemma dimension (hd : 0 < d) : HasDim (cosetComplex Hs) (d - 1) := by
  have hn : d - 1 + 1 = d := by omega
  constructor
  · intro f hf
    obtain ⟨g, hg⟩ := (face_iff Hs f).1 hf
    simpa [chamber_card Hs h1, hn] using Finset.card_le_card hg
  · refine ⟨chamber Hs 1, chamber_face Hs 1, ?_⟩
    rw [chamber_card Hs h1, hn]

include h1 in
lemma pure (hd : 0 < d) : IsPure (cosetComplex Hs) (d - 1) := by
  intro f hf hmax
  obtain ⟨g, hg⟩ := (face_iff Hs f).1 hf
  rw [← hmax (chamber Hs g) (chamber_face Hs g) hg, chamber_card Hs h1]
  omega

include h1 in
lemma coloring (hd : 0 < d) :
    ∃ r : Set F → Fin (d - 1 + 1), IsProperColoring (cosetComplex Hs) (d - 1) r := by
  classical
  have hn : d = d - 1 + 1 := by omega
  refine ⟨fun L => Fin.cast hn (color Hs hd L), ?_⟩
  intro u v hne hf he
  obtain ⟨g, hg⟩ := (face_iff Hs {u,v}).1 hf
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hg (by simp : u ∈ ({u,v} : Finset (Set F))))
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hg (by simp : v ∈ ({u,v} : Finset (Set F))))
  have hc : color Hs hd u = color Hs hd v := Fin.ext (congrArg (fun x : Fin (d - 1 + 1) => x.val) he)
  rw [← hi, ← hj, color_coset Hs h1, color_coset Hs h1] at hc
  exact hne (hi.symm.trans (hc ▸ hj))

include h1 in
lemma replacement : Replacement (cosetComplex Hs) := by
  classical
  intro f hf v hv
  obtain ⟨g, hg⟩ := (face_iff Hs f).1 hf
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hg hv)
  obtain ⟨z, hz, hnz⟩ := h1 i
  let u : Set F := (g * z) • (Hs i : Set F)
  refine ⟨u, ?_, ?_⟩
  · intro hu
    have hgu : g ∈ u := by
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hg hu)
      rw [← hj]
      exact center_mem (Hs j) g
    rcases hgu with ⟨h, hh, he⟩
    have hzh : z * h = 1 := mul_left_cancel (show g * (z * h) = g * 1 by simpa [mul_assoc] using he)
    have hez : z = h⁻¹ := by
      calc
        z = (z * h) * h⁻¹ := by simp [mul_assoc]
        _ = h⁻¹ := by rw [hzh, one_mul]
    apply hnz
    rw [hez]
    exact (Hs i).inv_mem hh
  · apply (face_iff Hs _).2
    refine ⟨g * z, ?_⟩
    intro L hL
    rcases Finset.mem_insert.mp hL with hL | hL
    · subst L
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · obtain ⟨hne, hLf⟩ := Finset.mem_erase.mp hL
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hg hLf)
      have hji : j ≠ i := by
        intro he
        apply hne
        exact hj.symm.trans (he ▸ hi)
      have he : g • (Hs j : Set F) = (g * z) • (Hs j : Set F) :=
        anchor (Hs j) ⟨z, hz j hji, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he.symm.trans hj⟩

include h1 in
lemma good [Finite F] (hd : 0 < d) : IsGood (cosetComplex Hs) (d - 1) :=
  ⟨complex Hs, Set.toFinite _, dimension Hs h1 hd, pure Hs h1 hd,
    coloring Hs h1 hd, replacement Hs h1⟩

end CosetGood

open MulticlassDS.NatGap

theorem solution {F : Type*} [Group F] [Finite F] (d : ℕ) (hd : 1 < d)
    (Hs : Fin d → Subgroup F)
    (h1 : ∀ i : Fin d, ∃ z : F, (∀ j : Fin d, j ≠ i → z ∈ Hs j) ∧ z ∉ Hs i)
    (h2 : NoEmptySquares (cosetComplex Hs)) :
    IsGood (cosetComplex Hs) (d - 1) ∧ NoEmptySquares (cosetComplex Hs) :=
  ⟨CosetGood.good Hs h1 (by omega), h2⟩

#print axioms solution
