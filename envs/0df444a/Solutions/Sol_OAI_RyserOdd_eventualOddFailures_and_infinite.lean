-- Prove2me | solution 1 for OAI.RyserOdd.eventualOddFailures_and_infinite
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-03T23:25:42.142646+00:00
-- url     : https://prove2.me/submissions/064514be-3f65-48c7-8688-8257c54d3a84

import Mathlib
import Definitions.Def_RyserOddSupport
import Theorems.Thm_OAI_RyserCoveringCounterexample_LineCover_uniform_linecover_probability_oddExt
import Theorems.Thm_OAI_RyserCoveringCounterexample_Selection_compatible_selection_uniform_oddExt

set_option Elab.async false
set_option linter.all false

section
namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

def lineThrough (d : Direction F) (p : Point F) : AffineLine F :=
  (d, projection d p)

@[simp] theorem projection_none (p : Point F) : projection none p = p.1 := rfl
@[simp] theorem projection_some (a : F) (p : Point F) :
    projection (some a) p = p.2 - a * p.1 := rfl
@[simp] theorem projection_some_zero (p : Point F) :
    projection (some 0) p = p.2 := by simp [projection]

@[simp] theorem incidence_mk (p : Point F) (d : Direction F) (b : F) :
    Incidence p (d, b) ↔ projection d p = b := Iff.rfl

@[simp] theorem lineThrough_direction (d : Direction F) (p : Point F) :
    (lineThrough d p).1 = d := rfl
@[simp] theorem lineThrough_offset (d : Direction F) (p : Point F) :
    (lineThrough d p).2 = projection d p := rfl
@[simp] theorem incidence_lineThrough (d : Direction F) (p : Point F) :
    Incidence p (lineThrough d p) := rfl

@[simp] theorem incidence_lineThrough_iff (d : Direction F) (p q : Point F) :
    Incidence p (lineThrough d q) ↔ projection d p = projection d q := Iff.rfl

theorem eq_lineThrough_of_incidence {p : Point F} {l : AffineLine F}
    (h : Incidence p l) : l = lineThrough l.1 p := by
  apply Prod.ext
  · rfl
  · exact h.symm

theorem projection_add (d : Direction F) (p q : Point F) :
    projection d (p.1 + q.1, p.2 + q.2) = projection d p + projection d q := by
  cases d with
  | none => rfl
  | some slope => simp only [projection]; ring

theorem projection_sub (d : Direction F) (p q : Point F) :
    projection d (p.1 - q.1, p.2 - q.2) = projection d p - projection d q := by
  cases d with
  | none => rfl
  | some slope => simp only [projection]; ring

@[simp] theorem projectiveIncidence_finite_affine (p : Point F) (l : AffineLine F) :
    ProjectiveIncidence (Sum.inl p) (some l) ↔ Incidence p l := Iff.rfl
@[simp] theorem projectiveIncidence_infinite_affine (d : Direction F) (l : AffineLine F) :
    ProjectiveIncidence (Sum.inr d) (some l) ↔ d = l.1 := Iff.rfl
@[simp] theorem projectiveIncidence_finite_infinity (p : Point F) :
    ¬ ProjectiveIncidence (Sum.inl p) (none : ProjectiveLine F) := not_false
@[simp] theorem projectiveIncidence_infinite_infinity (d : Direction F) :
    ProjectiveIncidence (Sum.inr d) (none : ProjectiveLine F) := trivial

section Finite
variable [Fintype F] [DecidableEq F]

def affinePencil (p : ProjectivePoint F) : Finset (AffineLine F) :=
  Finset.univ.filter fun l => ProjectiveIncidence p (some l)

def projectiveLinePoints (l : ProjectiveLine F) : Finset (ProjectivePoint F) :=
  Finset.univ.filter fun p => ProjectiveIncidence p l

def projectivePencil (p : ProjectivePoint F) : Finset (ProjectiveLine F) :=
  Finset.univ.filter fun l => ProjectiveIncidence p l

@[simp] theorem mem_linePoints (p : Point F) (l : AffineLine F) :
    p ∈ linePoints l ↔ Incidence p l := by simp only [linePoints, Finset.mem_filter,
    Finset.mem_univ, true_and]

@[simp] theorem mem_affinePencil (p : ProjectivePoint F) (l : AffineLine F) :
    l ∈ affinePencil p ↔ ProjectiveIncidence p (some l) := by
  simp only [affinePencil, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_projectiveLinePoints (p : ProjectivePoint F) (l : ProjectiveLine F) :
    p ∈ projectiveLinePoints l ↔ ProjectiveIncidence p l := by
  simp only [projectiveLinePoints, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_projectivePencil (p : ProjectivePoint F) (l : ProjectiveLine F) :
    l ∈ projectivePencil p ↔ ProjectiveIncidence p l := by
  simp only [projectivePencil, Finset.mem_filter, Finset.mem_univ, true_and]

end Finite
end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

def cubeMap (p : Point F) : Point F := (p.1 ^ 3, p.2)

def cubicPoint (d z x : F) : Point F := (x ^ 3, d * x + z)

theorem cubicPoint_injective (d z : F) (hd : d ≠ 0) :
    Function.Injective (cubicPoint d z) := by
  intro x y h
  exact mul_left_cancel₀ hd (add_right_cancel (congrArg Prod.snd h))

variable [instFintypeF : Fintype F]

theorem cube_bijective (h : Nat.Coprime 3 (Fintype.card F - 1)) :
    Function.Bijective (fun x : F => x ^ 3) := by
  classical
  have hU : (Nat.card Fˣ).Coprime 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact h.symm
  have hpow : Function.Bijective (fun u : Fˣ => u ^ 3) :=
    Nat.Coprime.pow_left_bijective hU
  apply Function.Surjective.bijective_of_finite
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp⟩
  · obtain ⟨u, hu⟩ := hpow.surjective (Units.mk0 y hy)
    refine ⟨(u : F), ?_⟩
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
      congrArg (fun v : Fˣ => (v : F)) hu

theorem cubeMap_bijective (h : Nat.Coprime 3 (Fintype.card F - 1)) :
    Function.Bijective (cubeMap : Point F → Point F) := by
  have hc := cube_bijective h
  constructor
  · intro p q hpq
    have hx := congrArg (fun r : Point F => r.1) hpq
    have hy := congrArg (fun r : Point F => r.2) hpq
    exact Prod.ext (hc.injective hx) hy
  · rintro ⟨x, y⟩
    obtain ⟨z, hz⟩ := hc.surjective x
    exact ⟨(z, y), Prod.ext hz rfl⟩

variable [instDecidableEqF : DecidableEq F]

def cubicShape (d z : F) : Finset (Point F) :=
  Finset.univ.image (cubicPoint d z)

@[simp] theorem mem_cubicShape {d z : F} {p : Point F} :
    p ∈ cubicShape d z ↔ ∃ x, cubicPoint d z x = p := by
  simp [cubicShape]

theorem cubicShape_card (d z : F) (hd : d ≠ 0) :
    (cubicShape d z).card = Fintype.card F := by
  rw [cubicShape, Finset.card_image_of_injective _ (cubicPoint_injective d z hd),
    Finset.card_univ]

theorem cubicShape_eq_image_linePoints (d z : F) :
    cubicShape d z = (linePoints (some d, z)).image cubeMap := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := mem_cubicShape.mp hp
    refine Finset.mem_image.mpr ⟨(x, d * x + z), ?_, rfl⟩
    apply (mem_linePoints _ _).mpr
    change d * x + z - d * x = z
    ring
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine mem_cubicShape.mpr ⟨q.1, ?_⟩
    apply Prod.ext
    · rfl
    · have hq' : q.2 - d * q.1 = z := (mem_linePoints _ _).mp hq
      change d * q.1 + z = q.2
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hq').symm

open Polynomial

def cubicLinePolynomial (d z : F) : AffineLine F → F[X]
  | (none, b) => X ^ 3 - C b
  | (some m, b) => C d * X + C z - C m * X ^ 3 - C b

theorem eval_cubicLinePolynomial_eq_zero_iff (d z : F) (l : AffineLine F) (x : F) :
    (cubicLinePolynomial d z l).eval x = 0 ↔ Incidence (cubicPoint d z x) l := let _ := instFintypeF; let _ := instDecidableEqF; by
  obtain ⟨a, b⟩ := l
  cases a <;>
    simp [cubicLinePolynomial, cubicPoint, Incidence, projection, sub_eq_zero]

theorem cubicLinePolynomial_ne_zero (d z : F) (hd : d ≠ 0) (l : AffineLine F) :
    cubicLinePolynomial d z l ≠ 0 := let _ := instFintypeF; let _ := instDecidableEqF; by
  obtain ⟨a, b⟩ := l
  cases a with
  | none =>
      intro hp
      have hc := congrArg (fun p : F[X] => p.coeff 3) hp
      exact (one_ne_zero : (1 : F) ≠ 0)
        (by simp [cubicLinePolynomial, coeff_X_pow] at hc)
  | some m =>
      intro hp
      have hc := congrArg (fun p : F[X] => p.coeff 1) hp
      exact hd (by simpa [cubicLinePolynomial, coeff_X_pow] using hc)

theorem cubicLinePolynomial_natDegree_le (d z : F) (l : AffineLine F) :
    (cubicLinePolynomial d z l).natDegree ≤ 3 := let _ := instFintypeF; let _ := instDecidableEqF; by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn3 : n ≠ 3 := by omega
  obtain ⟨a, b⟩ := l
  cases a <;>
    simp [cubicLinePolynomial, coeff_X_pow, coeff_C, coeff_X,
      hn0, Ne.symm hn1, hn3]

theorem cubicShape_filter_incidence_card_le (d z : F) (hd : d ≠ 0)
    (l : AffineLine F) :
    ((cubicShape d z).filter (fun p => Incidence p l)).card ≤ 3 := by
  have hcount :
      (Finset.univ.filter (fun x => Incidence (cubicPoint d z x) l)).card ≤
        (cubicLinePolynomial d z l).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    exact (Polynomial.mem_roots (cubicLinePolynomial_ne_zero d z hd l)).2
      ((eval_cubicLinePolynomial_eq_zero_iff d z l x).2 (Finset.mem_filter.mp hx).2)
  rw [cubicShape, Finset.filter_image]
  exact (Finset.card_image_le.trans hcount).trans (cubicLinePolynomial_natDegree_le d z l)

theorem cubicShape_inter_linePoints_card_le (d z : F) (hd : d ≠ 0)
    (l : AffineLine F) :
    (cubicShape d z ∩ linePoints l).card ≤ 3 := by
  have heq : cubicShape d z ∩ linePoints l =
      (cubicShape d z).filter (fun p => Incidence p l) := by
    ext p
    simp
  rw [heq]
  exact cubicShape_filter_incidence_card_le d z hd l

theorem cubicShape_ne_linePoints (d z : F) (hd : d ≠ 0)
    (hcard : 3 < Fintype.card F) (l : AffineLine F) :
    cubicShape d z ≠ linePoints l := by
  intro heq
  have hall : (cubicShape d z).filter (fun p => Incidence p l) = cubicShape d z := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact (mem_linePoints _ _).mp (heq ▸ hp)
  have hle := cubicShape_filter_incidence_card_le d z hd l
  rw [hall, cubicShape_card d z hd] at hle
  exact (not_le_of_gt hcard) hle

theorem cubicShape_intercept_unique (h : Nat.Coprime 3 (Fintype.card F - 1))
    (d : F) (p : Point F) : ∃! z, p ∈ cubicShape d z := by
  obtain ⟨x, hx⟩ := (cube_bijective h).surjective p.1
  refine ⟨p.2 - d * x, ?_, ?_⟩
  · refine mem_cubicShape.mpr ⟨x, ?_⟩
    apply Prod.ext
    · exact hx
    · change d * x + (p.2 - d * x) = p.2
      ring
  · intro z hz
    obtain ⟨y, hy⟩ := mem_cubicShape.mp hz
    have hyx : y = x :=
      (cube_bijective h).injective ((congrArg Prod.fst hy).trans hx.symm)
    subst y
    apply eq_sub_iff_add_eq.mpr
    simpa [cubicPoint, add_comm] using congrArg Prod.snd hy

theorem cubicShape_intercept_card (h : Nat.Coprime 3 (Fintype.card F - 1))
    (d : F) (p : Point F) :
    (Finset.univ.filter (fun z => p ∈ cubicShape d z)).card = 1 := by
  obtain ⟨z, hz, hu⟩ := cubicShape_intercept_unique h d p
  apply Finset.card_eq_one.mpr
  refine ⟨z, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨hu w, fun hw => hw ▸ hz⟩

theorem coprime_three_zmod_card_sub_one {p : ℕ} [Fact p.Prime] (hpmod : p % 3 = 2) :
    Nat.Coprime 3 (Fintype.card (ZMod p) - 1) := by
  rw [ZMod.card]
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

abbrev NonzeroSlope (k : Type*) [Zero k] := {d : k // d ≠ 0}

abbrev GadgetOutcome (k : Type*) [Zero k] := NonzeroSlope k → k

def omittedLine (a : GadgetOutcome k) (d : NonzeroSlope k) : AffineLine k :=
  (some d.val, a d)

def retainedPoints (a : GadgetOutcome k) : Finset (Point k) :=
  Finset.univ \ Finset.univ.biUnion (fun d => linePoints (omittedLine a d))

def transformedRetained (a : GadgetOutcome k) : Finset (Point k) :=
  (retainedPoints a).image cubeMap

def cubicDeletionUnion (a : GadgetOutcome k) : Finset (Point k) :=
  Finset.univ.biUnion fun d : NonzeroSlope k => cubicShape d.val (a d)

@[simp] theorem mem_retainedPoints (a : GadgetOutcome k) (w : Point k) :
    w ∈ retainedPoints a ↔ ∀ d, ¬Incidence w (omittedLine a d) := by
  simp [retainedPoints]

theorem not_incidence_omittedLine (a : GadgetOutcome k) {w : Point k}
    (hw : w ∈ retainedPoints a) (d : NonzeroSlope k) :
    ¬Incidence w (omittedLine a d) := (mem_retainedPoints a w).mp hw d

theorem cubeMap_mem_cubicShape_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (w : Point k) (d z : k) :
    cubeMap w ∈ cubicShape d z ↔ Incidence w (some d, z) := by
  rw [cubicShape_eq_image_linePoints]
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    have hsame : v = w := (cubeMap_bijective hcop).injective hvw
    subst v
    exact (mem_linePoints _ _).mp hv
  · intro hw
    exact Finset.mem_image.mpr ⟨w, (mem_linePoints _ _).mpr hw, rfl⟩

theorem cubeMap_mem_transformedRetained_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (a : GadgetOutcome k) (w : Point k) :
    cubeMap w ∈ transformedRetained a ↔ w ∈ retainedPoints a := by
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    exact (cubeMap_bijective hcop).injective hvw ▸ hv
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

theorem transformedRetained_eq_survivors
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (a : GadgetOutcome k) :
    transformedRetained a = Finset.univ \ cubicDeletionUnion a := by
  ext p
  obtain ⟨w, rfl⟩ := (cubeMap_bijective hcop).surjective p
  rw [cubeMap_mem_transformedRetained_iff hcop]
  simp [mem_retainedPoints, cubicDeletionUnion, cubeMap_mem_cubicShape_iff hcop,
    omittedLine]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]

def emptyOutcome (shapes : Finset (Finset P)) (D : ℕ) : Outcome shapes D :=
  ⟨∅, by simp⟩

variable {shapes : Finset (Finset P)} {D n : ℕ}

@[simp] theorem mem_deleted {ignore : Finset (Finset P)}
    {a : Outcome shapes D} {x : P} :
    x ∈ deleted ignore a ↔ ∃ L ∈ a.val, L.val ∉ ignore ∧ x ∈ L.val := by
  simp [deleted, Finset.mem_biUnion, and_assoc]

@[simp] theorem deleted_emptyOutcome (ignore : Finset (Finset P)) :
    deleted ignore (emptyOutcome shapes D) = ∅ := by
  simp [deleted, emptyOutcome]

def selected (ω : Fin n → Outcome shapes D) : Finset (Finset P) :=
  Finset.univ.biUnion (fun i => (ω i).val.image Subtype.val)

@[simp] theorem mem_selected {ω : Fin n → Outcome shapes D} {L : Finset P} :
    L ∈ selected ω ↔ ∃ i, ∃ s ∈ (ω i).val, s.val = L := by
  simp [selected, Finset.mem_biUnion, Finset.mem_image]

variable [instFintypeP : Fintype P]

@[simp] theorem mem_survivors {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {x : P} :
    x ∈ survivors ignore ω ↔ ∀ i, x ∉ deleted ignore (ω i) := by
  simp [survivors, Finset.mem_biUnion]

theorem mem_survivors_active {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {x : P} :
    x ∈ survivors ignore ω ↔ ∀ L ∈ selected ω \ ignore, x ∉ L := by
  rw [mem_survivors]
  constructor
  · intro h L hL hxL
    rcases Finset.mem_sdiff.mp hL with ⟨hsel, hI⟩
    rcases mem_selected.mp hsel with ⟨i, s, hs, rfl⟩
    exact h i (mem_deleted.mpr ⟨s, hs, hI, hxL⟩)
  · intro h i hx
    rcases mem_deleted.mp hx with ⟨s, hs, hI, hxs⟩
    exact h s.val (Finset.mem_sdiff.mpr
      ⟨mem_selected.mpr ⟨i, s, hs, rfl⟩, hI⟩) hxs

theorem survivors_insert_eq_of_not_selected
    {ignore : Finset (Finset P)} {ω : Fin n → Outcome shapes D}
    {L : Finset P} (hL : L ∉ selected ω) :
    survivors (insert L ignore) ω = survivors ignore ω := by
  ext x
  rw [mem_survivors_active, mem_survivors_active,
    Finset.sdiff_insert_of_notMem hL ignore]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open scoped Classical

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

abbrev LineTuple (F : Type*) (t : ℕ) := (Fin t ⊕ Fin t) ↪ AffineLine F

def crossPoints {t : ℕ} (a : LineTuple F t) : Finset (Point F) :=
  Finset.univ.filter fun x =>
    ∃ i j, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j))

def tupleShapes {t : ℕ} (a : LineTuple F t) : Finset (Finset (Point F)) :=
  Finset.univ.image fun i => linePoints (a i)

@[simp] theorem mem_crossPoints {t : ℕ} (a : LineTuple F t) (x : Point F) :
    x ∈ crossPoints a ↔
      ∃ i j, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j)) := by
  simp only [crossPoints, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_tupleShapes {t : ℕ} (a : LineTuple F t)
    (S : Finset (Point F)) :
    S ∈ tupleShapes a ↔ ∃ i, linePoints (a i) = S := by
  simp only [tupleShapes, Finset.mem_image, Finset.mem_univ, true_and]

@[simp] theorem mem_coverPencil (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (l : AffineLine F) :
    l ∈ coverPencil L p ↔ l ∈ L ∧ ProjectiveIncidence p (some l) := let _ := instFintypeF; by
  simp only [coverPencil, Finset.mem_filter]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable (k : Type*) [Field k] [Fintype k] [DecidableEq k]

def cubicShapes : Finset (Finset (Point k)) :=
  Finset.univ.image fun dz : NonzeroSlope k × k => cubicShape dz.1.val dz.2

theorem cubicShapes_card_le_square : (cubicShapes k).card ≤ Fintype.card k ^ 2 := by
  calc
    (cubicShapes k).card ≤
        (Finset.univ : Finset (NonzeroSlope k × k)).card :=
      Finset.card_image_le
    _ = Fintype.card (NonzeroSlope k) * Fintype.card k := by
      rw [Finset.card_univ, Fintype.card_prod]
    _ ≤ Fintype.card k * Fintype.card k :=
      Nat.mul_le_mul_right _
        (Fintype.card_subtype_le (fun d : k => d ≠ 0))
    _ = Fintype.card k ^ 2 := (pow_two _).symm

theorem cubicShapes_card_le : (cubicShapes k).card ≤ 3 * Fintype.card k ^ 3 := by
  have hq : 1 ≤ Fintype.card k := Nat.succ_le_of_lt Fintype.card_pos
  have hstep : Fintype.card k ^ 2 ≤ Fintype.card k ^ 3 := by
    rw [pow_succ (Fintype.card k) 2]
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left (Fintype.card k ^ 2) hq)
  exact (cubicShapes_card_le_square k).trans (hstep.trans (by omega))

variable {k}

@[simp] theorem mem_cubicShapes {S : Finset (Point k)} :
    S ∈ cubicShapes k ↔ ∃ d : NonzeroSlope k, ∃ z : k, cubicShape d.val z = S := by
  simp only [cubicShapes, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]

theorem cubicShape_mem_cubicShapes (d : NonzeroSlope k) (z : k) :
    cubicShape d.val z ∈ cubicShapes k :=
  Finset.mem_image.mpr ⟨(d, z), Finset.mem_univ _, rfl⟩

theorem cubicShapes_member_card {S : Finset (Point k)} (hS : S ∈ cubicShapes k) :
    S.card = Fintype.card k := by
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_card d.val z d.property

theorem cubicShapes_member_card_le {S : Finset (Point k)} (hS : S ∈ cubicShapes k) :
    S.card ≤ 3 * Fintype.card k := by
  rw [cubicShapes_member_card hS]
  omega

variable (k) in
theorem cubicShapes_sparse : LineCover.SparseShapes (cubicShapes k) 3 := by
  intro S hS ell _
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_inter_linePoints_card_le d.val z d.property ell

theorem cubicShapes_member_ne_linePoints (hcard : 3 < Fintype.card k)
    {S : Finset (Point k)} (hS : S ∈ cubicShapes k) (ell : AffineLine k) :
    S ≠ linePoints ell := by
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_ne_linePoints d.val z d.property hcard ell

def cubicTrialOutcome (d : NonzeroSlope k) (z : k) :
    LineCover.Outcome (cubicShapes k) 3 :=
  ⟨{⟨cubicShape d.val z, cubicShape_mem_cubicShapes d z⟩}, by simp⟩

@[simp] theorem cubicTrialOutcome_val (d : NonzeroSlope k) (z : k) :
    (cubicTrialOutcome d z).val =
      {⟨cubicShape d.val z, cubicShape_mem_cubicShapes d z⟩} := rfl

@[simp] theorem mem_deleted_cubicTrialOutcome (ignore : Finset (Finset (Point k)))
    (d : NonzeroSlope k) (z : k) (x : Point k) :
    x ∈ LineCover.deleted ignore (cubicTrialOutcome d z) ↔
      cubicShape d.val z ∉ ignore ∧ x ∈ cubicShape d.val z := by
  simp [LineCover.mem_deleted, cubicTrialOutcome]

@[simp] theorem deleted_empty_cubicTrialOutcome (d : NonzeroSlope k) (z : k) :
    LineCover.deleted ∅ (cubicTrialOutcome d z) = cubicShape d.val z := by
  ext x
  simp only [mem_deleted_cubicTrialOutcome, Finset.notMem_empty, not_false_eq_true, true_and]

@[simp] theorem mem_deleted_empty_cubicTrialOutcome
    (d : NonzeroSlope k) (z : k) (x : Point k) :
    x ∈ LineCover.deleted ∅ (cubicTrialOutcome d z) ↔ x ∈ cubicShape d.val z := by
  rw [deleted_empty_cubicTrialOutcome]

theorem cubicTrialOutcome_no_line (d : NonzeroSlope k) (z : k)
    (hcard : 3 < Fintype.card k) (ell : AffineLine k) :
    ¬ ∃ S ∈ (cubicTrialOutcome d z).val, S.val = linePoints ell := by
  rintro ⟨S, _, hline⟩
  exact cubicShapes_member_ne_linePoints hcard S.property ell hline

theorem selected_cubicShapes_ne_linePoints {n : ℕ}
    (ω : Fin n → LineCover.Outcome (cubicShapes k) 3)
    (hcard : 3 < Fintype.card k) {S : Finset (Point k)}
    (hS : S ∈ LineCover.selected ω) (ell : AffineLine k) : S ≠ linePoints ell := by
  obtain ⟨i, T, _, rfl⟩ := LineCover.mem_selected.mp hS
  exact cubicShapes_member_ne_linePoints hcard T.property ell

@[simp] theorem mem_selected_cubicTrials {n : ℕ}
    (d : Fin n → NonzeroSlope k) (z : Fin n → k) (S : Finset (Point k)) :
    S ∈ LineCover.selected (fun i => cubicTrialOutcome (d i) (z i)) ↔
      ∃ i, cubicShape (d i).val (z i) = S := by
  simp [LineCover.mem_selected, cubicTrialOutcome]

@[simp] theorem mem_survivors_cubicTrials {n : ℕ}
    (ignore : Finset (Finset (Point k)))
    (d : Fin n → NonzeroSlope k) (z : Fin n → k) (x : Point k) :
    x ∈ LineCover.survivors ignore (fun i => cubicTrialOutcome (d i) (z i)) ↔
      ∀ i, cubicShape (d i).val (z i) ∉ ignore → x ∉ cubicShape (d i).val (z i) := by
  simp only [LineCover.mem_survivors, mem_deleted_cubicTrialOutcome, not_and]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample

namespace FiniteLaw

def expectation {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * f ω

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

@[simp] theorem expectation_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, μ.total, one_mul]

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω + g ω) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω - g ω) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i, f i ω) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

@[simp] theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.total]

@[simp] theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.prob P := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [μ.nonneg]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob (fun ω => ¬ P ω) = 1 - μ.prob P := by
  classical
  have h : μ.prob P + μ.prob (fun ω => ¬ P ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

theorem prob_union_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.prob (fun ω => P ω ∨ Q ω) ≤ μ.prob P + μ.prob Q := by
  classical
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg]

theorem prob_le_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hP : ∀ ω, P ω → 1 ≤ f ω) : μ.prob P ≤ μ.expectation f := by
  classical
  rw [prob_eq_expectation]
  apply μ.expectation_mono
  intro ω
  by_cases hp : P ω
  · simpa [hp] using hP ω hp
  · simpa [hp] using hf ω

def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

@[simp] theorem prod_weight (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (ω : Ω) (γ : Γ) :
    (μ.prod ν).weight (ω, γ) = μ.weight ω * ν.weight γ := rfl

@[simp] theorem pi_weight {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) (ω : ∀ i, A i) :
    (pi μ).weight ω = ∏ i, (μ i).weight (ω i) := rfl

def iid (μ : FiniteLaw Ω) (n : ℕ) : FiniteLaw (Fin n → Ω) := pi (fun _ : Fin n => μ)

@[simp] theorem iid_weight (μ : FiniteLaw Ω) (n : ℕ) (ω : Fin n → Ω) :
    (iid μ n).weight ω = ∏ i, μ.weight (ω i) := rfl

theorem uniform_prob (Ω : Type*) [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    (uniform Ω).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  simp [prob, uniform, ← Finset.sum_filter, div_eq_mul_inv]

@[ext] theorem ext_weight {mu nu : FiniteLaw Ω} (h : mu.weight = nu.weight) :
    mu = nu := by
  cases mu
  cases nu
  cases h
  rfl

theorem eq_uniform_of_weight_eq [Nonempty Ω] (mu : FiniteLaw Ω)
    (h : ∀ x y, mu.weight x = mu.weight y) : mu = uniform Ω := by
  apply ext_weight
  funext x
  change mu.weight x = (Fintype.card Ω : ℝ)⁻¹
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (Fintype.card Ω : ℝ) * mu.weight x = 1 := by
    calc
      _ = ∑ y : Ω, mu.weight x := by simp
      _ = ∑ y : Ω, mu.weight y :=
        Finset.sum_congr rfl (fun y _ => (h y x).symm)
      _ = 1 := mu.total
  calc
    mu.weight x = (Fintype.card Ω : ℝ)⁻¹ *
        ((Fintype.card Ω : ℝ) * mu.weight x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    _ = (Fintype.card Ω : ℝ)⁻¹ := by rw [hsum, mul_one]

theorem prob_exists_le {ι : Type*} [Fintype ι] (mu : FiniteLaw Ω)
    (P : ι → Ω → Prop) :
    mu.prob (fun x => ∃ i, P i x) ≤ ∑ i, mu.prob (P i) := by
  classical
  have hn (i : ι) (x : Ω) : 0 ≤ (if P i x then (1 : ℝ) else 0) := by
    by_cases hix : P i x <;> simp [hix]
  calc
    _ ≤ mu.expectation (fun x => ∑ i, if P i x then (1 : ℝ) else 0) := by
      apply mu.prob_le_expectation
      · exact fun x => Finset.sum_nonneg (fun i _ => hn i x)
      · rintro x ⟨i, hi⟩
        calc
          1 = (if P i x then (1 : ℝ) else 0) := by rw [ite_eq_left hi]
          _ ≤ ∑ j, if P j x then (1 : ℝ) else 0 :=
            Finset.single_le_sum (fun j _ => hn j x) (Finset.mem_univ i)
    _ = ∑ i, mu.prob (P i) := by
      rw [expectation_sum]
      simp_rw [← prob_eq_expectation]

end FiniteLaw

end RyserCoveringCounterexample

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.FiniteLaw

section ProductCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

theorem expectation_pi_product (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (μ i).expectation (f i) := by
  classical
  simp only [expectation, pi_weight]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (μ i).weight a * f i a)).symm

theorem expectation_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (f : A i → ℝ) :
    (pi μ).expectation (fun ω => f (ω i)) = (μ i).expectation f := by
  classical
  let g : ∀ j, A j → ℝ := fun j a => if h : j = i then f (h ▸ a) else 1
  have hg (ω : ∀ j, A j) : (∏ j, g j (ω j)) = f (ω i) := by
    dsimp only [g]
    simp only [Fintype.prod_dite_eq']
  have he (j : I) : (μ j).expectation (g j) =
      if h : j = i then (μ i).expectation f else 1 := by
    by_cases h : j = i
    · subst j
      simp [g]
    · simp [g, h, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ j, g j (ω j)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ j, (μ j).expectation (g j) := expectation_pi_product μ g
    _ = _ := by simp_rw [he]; simp

theorem prob_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (P : A i → Prop) :
    (pi μ).prob (fun ω => P (ω i)) = (μ i).prob P := by
  classical
  rw [prob_eq_expectation, prob_eq_expectation]
  exact expectation_pi_coordinate μ i (fun a => if P a then 1 else 0)

theorem prob_pi (μ : ∀ i, FiniteLaw (A i)) (P : ∀ i, A i → Prop) :
    (pi μ).prob (fun ω => ∀ i, P i (ω i)) = ∏ i, (μ i).prob (P i) := by
  classical
  rw [prob_eq_expectation]
  calc
    _ = (pi μ).expectation (fun ω => ∏ i, if P i (ω i) then 1 else 0) := by
      congr 1
      funext ω
      symm
      by_cases h : ∀ i, P i (ω i)
      · simpa only [ite_eq_left h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
      · simpa only [ite_eq_right h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
    _ = ∏ i, (μ i).expectation (fun a => if P i a then 1 else 0) :=
      expectation_pi_product μ (fun i a => if P i a then 1 else 0)
    _ = _ := by simp_rw [prob_eq_expectation]

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def map (μ : FiniteLaw Ω) (f : Ω → Γ) : FiniteLaw Γ where
  weight γ := ∑ ω, if f ω = γ then μ.weight ω else 0
  nonneg γ := Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl
  total := by
    rw [Finset.sum_comm]
    simpa using μ.total

@[simp] theorem map_weight (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = ∑ ω, if f ω = γ then μ.weight ω else 0 := rfl

theorem map_weight_eq_prob (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = μ.prob (fun ω => f ω = γ) := rfl

theorem expectation_map (μ : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → ℝ) :
    (map μ f).expectation g = μ.expectation (fun ω => g (f ω)) := by
  unfold expectation
  simp only [map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

theorem prob_map (μ : FiniteLaw Ω) (f : Ω → Γ) (P : Γ → Prop) :
    (map μ f).prob P = μ.prob (fun ω => P (f ω)) := by
  rw [prob_eq_expectation, expectation_map, prob_eq_expectation]

theorem map_uniform_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) :
    (uniform Ω).map e = uniform Γ := by
  classical
  apply ext_weight
  funext y
  simp [map, uniform, ← e.eq_symm_apply, Fintype.card_congr e]

theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    pi (fun i => uniform (A i)) = uniform (∀ i, A i) :=
  eq_uniform_of_weight_eq (pi (fun i => uniform (A i))) (fun _ _ => rfl)

section UniformSplit

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty Ω]

end UniformSplit

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.LineCover

private theorem log_one_quarter_le_neg_one : Real.log (1 / 4 : ℝ) ≤ -1 := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.le_log_one_add_of_nonneg (x := 3) (by norm_num)
    norm_num at h
    linarith
  rw [one_div, Real.log_inv]
  linarith

theorem one_quarter_le_survival_pow_pred (q : ℕ) (hq : 2 ≤ q) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ (q - 1) := by
  have hq1 : 1 ≤ q := le_trans (by decide : 1 ≤ 2) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqm : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hbase : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / (q : ℝ) := by
    field_simp [hq0.ne']
  have hb : (0 : ℝ) < 1 - 1 / (q : ℝ) := by
    rw [hbase]
    exact div_pos hqm hq0
  have hunit : ((q - 1 : ℕ) : ℝ) * (1 - (1 - 1 / (q : ℝ))⁻¹) = -1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one, hbase, inv_div]
    field_simp [hqm.ne']; ring
  have hlog := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos hb)
    (Nat.cast_nonneg (q - 1) : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))
  rw [hunit] at hlog
  apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1 / 4)
    (pow_pos hb (q - 1))).mp
  rw [Real.log_pow]
  exact log_one_quarter_le_neg_one.trans hlog

theorem one_quarter_le_survival_pow (q n : ℕ) (hq : 2 ≤ q) (hn : n ≤ q - 1) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ n := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hinv : 1 / (q : ℝ) ≤ 1 := (div_le_one hq0).2 (by linarith)
  have hb0 : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := sub_nonneg.mpr hinv
  have hb1 : 1 - 1 / (q : ℝ) ≤ 1 := by
    have hnonneg : (0 : ℝ) ≤ 1 / (q : ℝ) := div_nonneg (by norm_num) hq0.le
    linarith
  exact (one_quarter_le_survival_pow_pred q hq).trans
    (pow_le_pow_of_le_one hb0 hb1 hn)

theorem one_quarter_le_survival_pow_sub_two (q : ℕ) (hq : 2 ≤ q) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ (q - 2) :=
  one_quarter_le_survival_pow q (q - 2) hq (Nat.sub_le_sub_left (by decide : 1 ≤ 2) q)

theorem quarter_mul_le_survival_mean (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) / 4 ≤ (q : ℝ) * (1 - 1 / (q : ℝ)) ^ (q - 2) := by
  have h := mul_le_mul_of_nonneg_left (one_quarter_le_survival_pow_sub_two q hq)
    (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  simpa only [mul_one_div] using h

end RyserCoveringCounterexample.LineCover

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

theorem map_map {Ω Γ Λ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Λ]
    (mu : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → Λ) :
    (mu.map f).map g = mu.map (g ∘ f) := by
  apply ext_weight
  funext z
  simp only [map_weight_eq_prob, prob_map, Function.comp_apply]

theorem map_pi {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (mu : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → B i) :
    (pi mu).map (fun a i => f i (a i)) = pi (fun i => (mu i).map (f i)) := by
  apply ext_weight
  funext b
  rw [map_weight_eq_prob]
  calc
    (pi mu).prob (fun a => (fun i => f i (a i)) = b) =
        (pi mu).prob (fun a => ∀ i, f i (a i) = b i) := by
      congr 1
      funext a
      exact propext ⟨fun h i => congrFun h i, fun h => funext h⟩
    _ = ∏ i, (mu i).prob (fun a => f i a = b i) :=
      prob_pi mu (fun i a => f i a = b i)
    _ = (pi (fun i => (mu i).map (f i))).weight b := by
      simp only [pi_weight, map_weight_eq_prob]

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem nonzeroSlope_card (k : Type*) [Field k] [Fintype k] [DecidableEq k] :
    Fintype.card (NonzeroSlope k) = Fintype.card k - 1 := by
  change Fintype.card {d : k // ¬d = 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

def cubicTrialLaw (d : NonzeroSlope k) :
    FiniteLaw (LineCover.Outcome (cubicShapes k) 3) :=
  (FiniteLaw.uniform k).map (cubicTrialOutcome d)

theorem cubicTrialLaw_point_probability
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : NonzeroSlope k) (x : Point k) :
    (cubicTrialLaw d).prob (fun a => x ∈ LineCover.deleted ∅ a) =
      1 / (Fintype.card k : ℝ) := by
  rw [cubicTrialLaw, FiniteLaw.prob_map]
  simp only [deleted_empty_cubicTrialOutcome]
  rw [FiniteLaw.uniform_prob]
  have hfilter : @Finset.filter _ (fun z => x ∈ cubicShape d.val z)
      (fun z => Classical.propDecidable (x ∈ cubicShape d.val z)) Finset.univ =
      Finset.univ.filter (fun z => x ∈ cubicShape d.val z) :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter, cubicShape_intercept_card hcop]
  simp

theorem cubicTrialLaw_point_probability_le
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : NonzeroSlope k) (x : Point k) :
    (cubicTrialLaw d).prob (fun a => x ∈ LineCover.deleted ∅ a) ≤
      (3 : ℝ) / Fintype.card k := by
  rw [cubicTrialLaw_point_probability hcop]
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem cubicTrialLaw_line_probability_zero
    (hcard : 3 < Fintype.card k) (d : NonzeroSlope k) (l : AffineLine k) :
    (cubicTrialLaw d).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l) = 0 := by
  rw [cubicTrialLaw, FiniteLaw.prob_map]
  have hevent : (fun z : k => ∃ S ∈ (cubicTrialOutcome d z).val,
      S.val = linePoints l) = (fun _ : k => False) := by
    funext z
    exact propext (iff_false_intro (cubicTrialOutcome_no_line d z hcard l))
  rw [hevent, FiniteLaw.prob_false]

def gadgetSlope (i : Fin (Fintype.card (NonzeroSlope k))) : NonzeroSlope k :=
  (Fintype.equivFin (NonzeroSlope k)).symm i

def gadgetTrials (i : Fin (Fintype.card (NonzeroSlope k))) :
    FiniteLaw (LineCover.Outcome (cubicShapes k) 3) :=
  cubicTrialLaw (gadgetSlope i)

def gadgetSurvival (k : Type*) [Field k] [Fintype k] : ℝ :=
  (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 1)

theorem gadgetTrials_uniformSurvival
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (x : Point k) :
    (FiniteLaw.pi (gadgetTrials (k := k))).prob
      (fun a => x ∈ LineCover.survivors ∅ a) = gadgetSurvival k := by
  simp only [LineCover.mem_survivors]
  rw [FiniteLaw.prob_pi (gadgetTrials (k := k))
    (fun _ a => x ∉ LineCover.deleted ∅ a)]
  simp_rw [FiniteLaw.prob_compl]
  simp only [gadgetTrials, cubicTrialLaw_point_probability hcop]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    nonzeroSlope_card, gadgetSurvival]

def gadgetDeletionProcess
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hcard : 3 < Fintype.card k) (δ : ℝ)
    (hδ : δ ≤ gadgetSurvival k) : LineCover.DeletionProcess k 3 δ where
  shapes := cubicShapes k
  shapeCount := cubicShapes_card_le k
  shapeSize := by
    intro S hS
    exact cubicShapes_member_card_le hS
  sparse := cubicShapes_sparse k
  trialsCount := Fintype.card (NonzeroSlope k)
  trials := gadgetTrials
  trialsCount_le := by rw [nonzeroSlope_card]; omega
  pointCap := fun i x => cubicTrialLaw_point_probability_le hcop (gadgetSlope i) x
  survival := gadgetSurvival k
  survivalLower := hδ
  uniformSurvival := gadgetTrials_uniformSurvival hcop
  lineCap := by
    intro l
    have hzero : ∀ i : Fin (Fintype.card (NonzeroSlope k)),
        (gadgetTrials i).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l) = 0 :=
      fun i => cubicTrialLaw_line_probability_zero hcard (gadgetSlope i) l
    simp only [hzero, Finset.sum_const_zero]
    positivity

def cubicDeletionProcess
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hcard : 3 < Fintype.card k) : LineCover.DeletionProcess k 3 (1 / 4 : ℝ) :=
  gadgetDeletionProcess hcop hcard (1 / 4)
    (LineCover.one_quarter_le_survival_pow_pred (Fintype.card k) (by omega))

def gadgetLaw (k : Type*) [Field k] [Fintype k] [DecidableEq k] :
    FiniteLaw (GadgetOutcome k) :=
  FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)

def gadgetInterceptEquiv : GadgetOutcome k ≃
    (Fin (Fintype.card (NonzeroSlope k)) → k) where
  toFun a i := a (gadgetSlope i)
  invFun b d := b ((Fintype.equivFin (NonzeroSlope k)) d)
  left_inv a := by
    funext d
    simp only [gadgetSlope, Equiv.symm_apply_apply]
  right_inv b := by
    funext i
    simp only [gadgetSlope, Equiv.apply_symm_apply]

def gadgetConfig (a : GadgetOutcome k) :
    Fin (Fintype.card (NonzeroSlope k)) → LineCover.Outcome (cubicShapes k) 3 :=
  fun i => cubicTrialOutcome (gadgetSlope i) (a (gadgetSlope i))

theorem gadgetLaw_map_config :
    (gadgetLaw k).map gadgetConfig = FiniteLaw.pi (gadgetTrials (k := k)) := by
  let f : (Fin (Fintype.card (NonzeroSlope k)) → k) →
      (Fin (Fintype.card (NonzeroSlope k)) → LineCover.Outcome (cubicShapes k) 3) :=
    fun a i => cubicTrialOutcome (gadgetSlope i) (a i)
  have hconfig : gadgetConfig (k := k) = f ∘ gadgetInterceptEquiv := rfl
  rw [hconfig, ← FiniteLaw.map_map]
  have hreindex : (gadgetLaw k).map gadgetInterceptEquiv =
      FiniteLaw.pi (fun _ : Fin (Fintype.card (NonzeroSlope k)) =>
        FiniteLaw.uniform k) := by
    rw [gadgetLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv,
      FiniteLaw.pi_uniform]
  rw [hreindex]
  exact FiniteLaw.map_pi (fun _ => FiniteLaw.uniform k)
    (fun i => cubicTrialOutcome (gadgetSlope i))

theorem gadgetConfig_survivors
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (a : GadgetOutcome k) :
    LineCover.survivors ∅ (gadgetConfig a) = transformedRetained a := by
  rw [transformedRetained_eq_survivors hcop]
  ext x
  have hright : x ∈ Finset.univ \ cubicDeletionUnion a ↔
      ∀ d : NonzeroSlope k, x ∉ cubicShape d.val (a d) := by
    simp [cubicDeletionUnion]
  rw [hright, LineCover.mem_survivors]
  simp only [gadgetConfig, deleted_empty_cubicTrialOutcome]
  constructor
  · intro h d
    simpa only [gadgetSlope, Equiv.symm_apply_apply] using
      h ((Fintype.equivFin (NonzeroSlope k)) d)
  · intro h i
    exact h (gadgetSlope i)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem point_eq_of_projection_eq_of_ne_direction
    {d e : Direction F} {p q : Point F} (hde : d ≠ e)
    (hd : projection d p = projection d q)
    (he : projection e p = projection e q) : p = q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨z, w⟩
  cases d with
  | none =>
    cases e with
    | none => exact (hde rfl).elim
    | some b =>
      change x = z at hd
      change y - b * x = w - b * z at he
      apply Prod.ext hd
      calc
        y = (y - b * x) + b * x := by ring
        _ = (w - b * z) + b * z := by rw [he, hd]
        _ = w := by ring
  | some a =>
    cases e with
    | none =>
      change y - a * x = w - a * z at hd
      change x = z at he
      apply Prod.ext he
      calc
        y = (y - a * x) + a * x := by ring
        _ = (w - a * z) + a * z := by rw [hd, he]
        _ = w := by ring
    | some b =>
      have hab : a ≠ b := fun h => hde (congrArg Option.some h)
      change y - a * x = w - a * z at hd
      change y - b * x = w - b * z at he
      have hmul : (a - b) * x = (a - b) * z := by
        calc
          (a - b) * x = (y - b * x) - (y - a * x) := by ring
          _ = (w - b * z) - (w - a * z) := by rw [he, hd]
          _ = (a - b) * z := by ring
      have hx : x = z := mul_left_cancel₀ (sub_ne_zero.mpr hab) hmul
      apply Prod.ext hx
      calc
        y = (y - a * x) + a * x := by ring
        _ = (w - a * z) + a * z := by rw [hd, hx]
        _ = w := by ring

theorem line_eq_of_direction_eq_of_incidence
    {l m : AffineLine F} {p : Point F} (hdl : l.1 = m.1)
    (hpl : Incidence p l) (hpm : Incidence p m) : l = m := by
  change projection l.1 p = l.2 at hpl
  change projection m.1 p = m.2 at hpm
  apply Prod.ext hdl
  exact hpl.symm.trans ((congrArg (fun d => projection d p) hdl).trans hpm)

theorem line_eq_of_two_incident_points
    {p q : Point F} {l m : AffineLine F} (hpq : p ≠ q)
    (hpl : Incidence p l) (hql : Incidence q l)
    (hpm : Incidence p m) (hqm : Incidence q m) : l = m := by
  by_cases hdir : l.1 = m.1
  · exact line_eq_of_direction_eq_of_incidence hdir hpl hpm
  · change projection l.1 p = l.2 at hpl
    change projection l.1 q = l.2 at hql
    change projection m.1 p = m.2 at hpm
    change projection m.1 q = m.2 at hqm
    exact (hpq (point_eq_of_projection_eq_of_ne_direction hdir
      (hpl.trans hql.symm) (hpm.trans hqm.symm))).elim

theorem eq_of_common_incidence_of_ne_lines
    {l m : AffineLine F} {p q : Point F} (hlm : l ≠ m)
    (hpl : Incidence p l) (hpm : Incidence p m)
    (hql : Incidence q l) (hqm : Incidence q m) : p = q := by
  by_contra hpq
  exact hlm (line_eq_of_two_incident_points hpq hpl hql hpm hqm)

theorem existsUnique_incident_of_ne_direction (l m : AffineLine F)
    (hdir : l.1 ≠ m.1) :
    ∃! p : Point F, Incidence p l ∧ Incidence p m := by
  have hex : ∃ p : Point F, Incidence p l ∧ Incidence p m := by
    rcases l with ⟨d, b⟩
    rcases m with ⟨e, c⟩
    change d ≠ e at hdir
    cases d with
    | none =>
      cases e with
      | none => exact (hdir rfl).elim
      | some a =>
        refine ⟨(b, c + a * b), ?_⟩
        change b = b ∧ (c + a * b) - a * b = c
        exact ⟨rfl, by ring⟩
    | some a =>
      cases e with
      | none =>
        refine ⟨(c, b + a * c), ?_⟩
        change (b + a * c) - a * c = b ∧ c = c
        exact ⟨by ring, rfl⟩
      | some a' =>
        have haa : a ≠ a' := fun h => hdir (congrArg Option.some h)
        have hne : a - a' ≠ 0 := sub_ne_zero.mpr haa
        let x : F := (c - b) / (a - a')
        have hx : x * (a - a') = c - b := by
          change (c - b) / (a - a') * (a - a') = c - b
          exact div_mul_cancel₀ (c - b) hne
        refine ⟨(x, b + a * x), ?_⟩
        change (b + a * x) - a * x = b ∧ (b + a * x) - a' * x = c
        constructor
        · ring
        · calc
            (b + a * x) - a' * x = b + x * (a - a') := by ring
            _ = b + (c - b) := by rw [hx]
            _ = c := by ring
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro q hq
  change projection l.1 p = l.2 ∧ projection m.1 p = m.2 at hp
  change projection l.1 q = l.2 ∧ projection m.1 q = m.2 at hq
  exact point_eq_of_projection_eq_of_ne_direction hdir
    (hq.1.trans hp.1.symm) (hq.2.trans hp.2.symm)

section Join

variable [DecidableEq F]

def joinDirection (p q : Point F) : Direction F :=
  if p.1 = q.1 then none else some ((q.2 - p.2) / (q.1 - p.1))

def joinLine (p q : Point F) : AffineLine F :=
  lineThrough (joinDirection p q) p

@[simp] theorem incidence_joinLine_left (p q : Point F) :
    Incidence p (joinLine p q) := rfl

@[simp] theorem incidence_joinLine_right (p q : Point F) :
    Incidence q (joinLine p q) := by
  change projection (joinDirection p q) q = projection (joinDirection p q) p
  by_cases hx : p.1 = q.1
  · have hd : joinDirection p q = none := by
      unfold joinDirection
      exact ite_eq_left hx
    simpa only [hd, projection] using hx.symm
  · let a : F := (q.2 - p.2) / (q.1 - p.1)
    have hd : joinDirection p q = some a := by
      unfold joinDirection
      exact ite_eq_right hx
    have hden : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hs : a * (q.1 - p.1) = q.2 - p.2 := by
      change (q.2 - p.2) / (q.1 - p.1) * (q.1 - p.1) = q.2 - p.2
      exact div_mul_cancel₀ (q.2 - p.2) hden
    simp only [hd, projection]
    calc
      q.2 - a * q.1 = p.2 - a * p.1 +
          ((q.2 - p.2) - a * (q.1 - p.1)) := by ring
      _ = p.2 - a * p.1 := by rw [hs]; ring

theorem eq_joinLine_of_incidence {p q : Point F} {l : AffineLine F}
    (hpq : p ≠ q) (hpl : Incidence p l) (hql : Incidence q l) :
    l = joinLine p q :=
  line_eq_of_two_incident_points hpq hpl hql
    (incidence_joinLine_left p q) (incidence_joinLine_right p q)

theorem existsUnique_lineThrough_pair {p q : Point F} (hpq : p ≠ q) :
    ∃! l : AffineLine F, Incidence p l ∧ Incidence q l := by
  refine ⟨joinLine p q, ⟨incidence_joinLine_left p q,
    incidence_joinLine_right p q⟩, ?_⟩
  intro l hl
  exact eq_joinLine_of_incidence hpq hl.1 hl.2

end Join

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem existsUnique_projectiveLine_of_ne {p q : ProjectivePoint F}
    (hpq : p ≠ q) :
    ∃! l : ProjectiveLine F, ProjectiveIncidence p l ∧ ProjectiveIncidence q l := by
  classical
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hpq' : p ≠ q := fun h => hpq (congrArg Sum.inl h)
      obtain ⟨l, hl, huniq⟩ := existsUnique_lineThrough_pair hpq'
      refine ⟨some l, hl, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m => exact congrArg some (huniq m hm)
    | inr d =>
      refine ⟨some (lineThrough d p), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.2.symm hm.1 rfl
  | inr d =>
    cases q with
    | inl q =>
      refine ⟨some (lineThrough d q), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.2.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.1.symm hm.2 rfl
    | inr e =>
      refine ⟨none, ⟨trivial, trivial⟩, ?_⟩
      intro m hm
      cases m with
      | none => rfl
      | some m =>
        have hde : d = e := hm.1.trans hm.2.symm
        exact (hpq (congrArg Sum.inr hde)).elim

theorem eq_projectiveLine_of_common_incidence
    {p q : ProjectivePoint F} {l m : ProjectiveLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p l) (hql : ProjectiveIncidence q l)
    (hpm : ProjectiveIncidence p m) (hqm : ProjectiveIncidence q m) : l = m := by
  obtain ⟨k, _, huniq⟩ := existsUnique_projectiveLine_of_ne hpq
  exact (huniq l ⟨hpl, hql⟩).trans (huniq m ⟨hpm, hqm⟩).symm

theorem eq_affineLine_of_common_projective_incidence
    {p q : ProjectivePoint F} {l m : AffineLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p (some l))
    (hql : ProjectiveIncidence q (some l))
    (hpm : ProjectiveIncidence p (some m))
    (hqm : ProjectiveIncidence q (some m)) : l = m :=
  Option.some.inj (eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm)

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_linePoints_inter_le_one {l m : AffineLine F} (hlm : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact eq_of_common_incidence_of_ne_lines hlm
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hx).1)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hx).2)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hy).1)
    ((mem_linePoints _ _).mp (Finset.mem_inter.mp hy).2)

theorem covered_points_on_missing_pencil_line
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell)) (hell : ell ∉ L) :
    (X ∩ linePoints ell).card ≤ 1 + (L \ affinePencil p).card := by
  classical
  let T := X ∩ linePoints ell
  let A := T.filter fun x => Sum.inl x = p
  let R := L \ affinePencil p
  have hA : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact Sum.inl.inj ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm)
  have hintersection : ∀ m ∈ R, (T ∩ linePoints m).card ≤ 1 := by
    intro m hm
    have hmL : m ∈ L := (Finset.mem_sdiff.mp hm).1
    have hne : ell ≠ m := fun heq => hell (heq.symm ▸ hmL)
    apply le_trans (Finset.card_le_card ?_) (card_linePoints_inter_le_one hne)
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp hx).2⟩
  have hsub : T ⊆ A ∪ R.biUnion (fun m => T ∩ linePoints m) := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_inter.mp hx).1
    have hxell : Incidence x ell :=
      (mem_linePoints _ _).mp (Finset.mem_inter.mp hx).2
    obtain ⟨m, hmL, hxm⟩ := hcover x hxX
    by_cases hmp : m ∈ affinePencil p
    · have hxp : Sum.inl x = p := by
        by_contra hne
        have heq : ell = m := eq_affineLine_of_common_projective_incidence
          hne hxell hpell hxm ((mem_affinePencil _ _).mp hmp)
        exact hell (heq.symm ▸ hmL)
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxp⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_sdiff.mpr ⟨hmL, hmp⟩,
          Finset.mem_inter.mpr ⟨hx, (mem_linePoints _ _).mpr hxm⟩⟩
  calc
    (X ∩ linePoints ell).card = T.card := rfl
    _ ≤ (A ∪ R.biUnion (fun m => T ∩ linePoints m)).card :=
      Finset.card_le_card hsub
    _ ≤ A.card + (R.biUnion (fun m => T ∩ linePoints m)).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ m ∈ R, (T ∩ linePoints m).card :=
      Nat.add_le_add hA Finset.card_biUnion_le
    _ ≤ 1 + ∑ _m ∈ R, 1 := Nat.add_le_add_left (Finset.sum_le_sum hintersection) 1
    _ = 1 + (L \ affinePencil p).card := by simp [R]

theorem mem_cover_of_pencil_survivors
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell))
    (hmany : 1 + (L \ affinePencil p).card < (X ∩ linePoints ell).card) :
    ell ∈ L := by
  by_contra hell
  exact (not_le_of_gt hmany)
    (covered_points_on_missing_pencil_line X L p ell hcover hpell hell)

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [instFieldF : Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

@[simp] theorem card_point :
    Fintype.card (Point F) = Fintype.card F ^ 2 := let _ := instFieldF; let _ := instDecidableEqF; by
  simp only [Point, Fintype.card_prod, pow_two]

@[simp] theorem card_direction :
    Fintype.card (Direction F) = Fintype.card F + 1 := let _ := instFieldF; let _ := instDecidableEqF; by
  exact Fintype.card_option

@[simp] theorem card_affineLine :
    Fintype.card (AffineLine F) = Fintype.card F * (Fintype.card F + 1) := by
  simp only [AffineLine, Fintype.card_prod, card_direction, Nat.mul_comm]

@[simp] theorem card_projectivePoint :
    Fintype.card (ProjectivePoint F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectivePoint, Fintype.card_sum, card_point, card_direction, Nat.add_assoc]

@[simp] theorem card_projectiveLine :
    Fintype.card (ProjectiveLine F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectiveLine, Fintype.card_option, card_affineLine,
    Nat.mul_add, Nat.mul_one, pow_two]

def linePointEquiv (l : AffineLine F) : F ≃ ↥(linePoints l) := by
  rcases l with ⟨d, b⟩
  cases d with
  | none =>
      refine
        { toFun := fun t => ⟨(b, t), by simp [Incidence, projection]⟩
          invFun := fun p => p.val.2
          left_inv := fun _ => rfl
          right_inv := ?_ }
      intro p
      apply Subtype.ext
      apply Prod.ext
      · have hp := (mem_linePoints p.val (none, b)).mp p.property
        change p.val.1 = b at hp
        exact hp.symm
      · rfl
  | some a =>
      refine
        { toFun := fun t => ⟨(t, b + a * t), by simp [Incidence, projection]⟩
          invFun := fun p => p.val.1
          left_inv := fun _ => rfl
          right_inv := ?_ }
      intro p
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have hp := (mem_linePoints p.val (some a, b)).mp p.property
        change p.val.2 - a * p.val.1 = b at hp
        simpa only [sub_add_cancel] using
          (congrArg (fun u : F => u + a * p.val.1) hp).symm

@[simp] theorem card_linePoints (l : AffineLine F) :
    (linePoints l).card = Fintype.card F := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (linePointEquiv l)).symm

def affinePencilFiniteEquiv (p : Point F) :
    Direction F ≃ ↥(affinePencil (Sum.inl p)) where
  toFun d := ⟨lineThrough d p, by simp⟩
  invFun l := l.val.1
  left_inv _ := rfl
  right_inv l := by
    apply Subtype.ext
    have hl : Incidence p l.val :=
      (mem_affinePencil (Sum.inl p) l.val).mp l.property
    exact (eq_lineThrough_of_incidence hl).symm

def affinePencilInfiniteEquiv (d : Direction F) :
    F ≃ ↥(affinePencil (Sum.inr d)) where
  toFun b := ⟨(d, b), by simp⟩
  invFun l := l.val.2
  left_inv _ := rfl
  right_inv l := by
    apply Subtype.ext
    apply Prod.ext
    · exact (mem_affinePencil (Sum.inr d) l.val).mp l.property
    · rfl

@[simp] theorem card_affinePencil_finite (p : Point F) :
    (affinePencil (Sum.inl p)).card = Fintype.card F + 1 := by
  simpa only [Fintype.card_coe, card_direction] using
    (Fintype.card_congr (affinePencilFiniteEquiv p)).symm

@[simp] theorem card_affinePencil_infinite (d : Direction F) :
    (affinePencil (Sum.inr d)).card = Fintype.card F := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (affinePencilInfiniteEquiv d)).symm

theorem projectiveLinePoints_some (l : AffineLine F) :
    projectiveLinePoints (some l) = (linePoints l).disjSum {l.1} := by
  ext p
  cases p with
  | inl p => simp
  | inr d => simp

theorem projectiveLinePoints_none :
    projectiveLinePoints (none : ProjectiveLine F) =
      (∅ : Finset (Point F)).disjSum (Finset.univ : Finset (Direction F)) := by
  ext p
  cases p with
  | inl p => simp
  | inr d => simp

theorem projectivePencil_finite (p : Point F) :
    projectivePencil (Sum.inl p) =
      (affinePencil (Sum.inl p)).map Function.Embedding.some := by
  ext l
  cases l with
  | none => simp [Finset.mem_map]
  | some l => simp [Finset.mem_map]

theorem projectivePencil_infinite (d : Direction F) :
    projectivePencil (Sum.inr d) = (affinePencil (Sum.inr d)).insertNone := by
  ext l
  cases l with
  | none => simp
  | some l => simp

@[simp] theorem card_projectiveLinePoints (l : ProjectiveLine F) :
    (projectiveLinePoints l).card = Fintype.card F + 1 := by
  cases l with
  | none =>
      rw [projectiveLinePoints_none, Finset.card_disjSum, Finset.card_empty,
        Finset.card_univ, card_direction, Nat.zero_add]
  | some l =>
      rw [projectiveLinePoints_some, Finset.card_disjSum, card_linePoints,
        Finset.card_singleton]

@[simp] theorem card_projectivePencil (p : ProjectivePoint F) :
    (projectivePencil p).card = Fintype.card F + 1 := by
  cases p with
  | inl p =>
      rw [projectivePencil_finite, Finset.card_map, card_affinePencil_finite]
  | inr d =>
      rw [projectivePencil_infinite, Finset.card_insertNone, card_affinePencil_infinite]

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mixed_covered_points_on_missing_pencil_line
    (X B : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, x ∈ B ∨ ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell)) (hell : ell ∉ L) :
    (X ∩ linePoints ell).card ≤ 1 + (L \ affinePencil p).card + B.card := by
  have hlinecover : ∀ x ∈ X \ B, ∃ l ∈ L, Incidence x l := by
    intro x hx
    rcases hcover x (Finset.mem_sdiff.mp hx).1 with hxB | hxL
    · exact ((Finset.mem_sdiff.mp hx).2 hxB).elim
    · exact hxL
  have hbound := covered_points_on_missing_pencil_line (X \ B) L p ell
    hlinecover hpell hell
  have hsub : X ∩ linePoints ell ⊆ ((X \ B) ∩ linePoints ell) ∪ B := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right _ hxB
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1, hxB⟩,
          (Finset.mem_inter.mp hx).2⟩)
  calc
    (X ∩ linePoints ell).card ≤ (((X \ B) ∩ linePoints ell) ∪ B).card :=
      Finset.card_le_card hsub
    _ ≤ ((X \ B) ∩ linePoints ell).card + B.card := Finset.card_union_le _ _
    _ ≤ 1 + (L \ affinePencil p).card + B.card := Nat.add_le_add_right hbound _

theorem mixed_cover_eq_parallel_of_near_pencil
    (Y B : Finset (Point F)) (L : Finset (AffineLine F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell)
    (hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card F)
    (hnear : ∃ p : ProjectivePoint F,
      99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card) :
    ∃ d : Direction F, L = affinePencil (Sum.inr d) ∧ B = ∅ := by
  obtain ⟨p, hp⟩ := hnear
  have hLcard : L.card ≤ Fintype.card F := by omega
  have hdecomp := Finset.card_sdiff_add_card_inter L (affinePencil p)
  have hforced : affinePencil p ⊆ L := by
    intro ell hell
    by_contra hmissing
    have hpell : ProjectiveIncidence p (some ell) :=
      (mem_affinePencil _ _).mp hell
    have hcount := mixed_covered_points_on_missing_pencil_line Y B L p ell
      hcover hpell hmissing
    have hlower := hlines ell
    omega
  cases p with
  | inl p =>
      have hcard := Finset.card_le_card hforced
      rw [card_affinePencil_finite] at hcard
      omega
  | inr d =>
      have heq : affinePencil (Sum.inr d) = L :=
        Finset.eq_of_subset_of_card_le hforced (by simpa using hLcard)
      have hL : L.card = Fintype.card F := by rw [← heq, card_affinePencil_infinite]
      have hB : B.card = 0 := by omega
      exact ⟨d, heq.symm, Finset.card_eq_zero.mp hB⟩

theorem missed_points_subset_of_mixed_cover
    (Y B : Finset (Point F)) (L : Finset (AffineLine F))
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) :
    Y \ L.biUnion linePoints ⊆ B := by
  intro y hy
  rcases hcover y (Finset.mem_sdiff.mp hy).1 with hyB | ⟨ell, hell, hyell⟩
  · exact hyB
  · exact ((Finset.mem_sdiff.mp hy).2
      (Finset.mem_biUnion.mpr ⟨ell, hell, (mem_linePoints _ _).mpr hyell⟩)).elim

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def GadgetCoverProperty (Y : Finset (Point F)) : Prop :=
  ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
    (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
    2 * L.card + B.card ≤ 2 * Fintype.card F →
    ∃ d : Direction F, L = affinePencil (Sum.inr d) ∧ B = ∅

theorem gadgetCoverProperty_of_near_pencils
    (Y : Finset (Point F))
    (hlarge : 200 < 19 * Fintype.card F)
    (hlines : ∀ ell : AffineLine F,
      Fintype.card F ≤ 8 * (Y ∩ linePoints ell).card)
    (hnear : ∀ (B : Finset (Point F)) (L : Finset (AffineLine F)),
      (∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) →
      2 * L.card + B.card ≤ 2 * Fintype.card F →
      ∃ p : ProjectivePoint F,
        99 * Fintype.card F ≤ 100 * (L ∩ affinePencil p).card) :
    GadgetCoverProperty Y := by
  intro B L hcover hbudget
  exact mixed_cover_eq_parallel_of_near_pencil Y B L hlarge hlines
    hcover hbudget (hnear B L hcover hbudget)

theorem GadgetCoverProperty.weighted_card_lower_bound
    {Y : Finset (Point F)} (hY : GadgetCoverProperty Y)
    (B : Finset (Point F)) (L : Finset (AffineLine F))
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) :
    2 * Fintype.card F ≤ 2 * L.card + B.card := by
  by_cases hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card F
  · obtain ⟨d, hL, hB⟩ := hY B L hcover hbudget
    have hcard : L.card = Fintype.card F := by
      rw [hL, card_affinePencil_infinite]
    have hBcard : B.card = 0 := by rw [hB, Finset.card_empty]
    omega
  · omega

theorem GadgetCoverProperty.not_line_cover_of_distinct_directions
    {Y : Finset (Point F)} (hY : GadgetCoverProperty Y)
    (L : Finset (AffineLine F)) (hcard : L.card ≤ Fintype.card F)
    {ell m : AffineLine F} (hell : ell ∈ L) (hm : m ∈ L)
    (hdirections : ell.1 ≠ m.1) :
    ¬ (∀ y ∈ Y, ∃ l ∈ L, Incidence y l) := by
  intro hcover
  have hmixed : ∀ y ∈ Y,
      y ∈ (∅ : Finset (Point F)) ∨ ∃ l ∈ L, Incidence y l := by
    intro y hy
    exact Or.inr (hcover y hy)
  have hbudget : 2 * L.card + (∅ : Finset (Point F)).card ≤
      2 * Fintype.card F := by
    simpa only [Finset.card_empty, Nat.add_zero] using Nat.mul_le_mul_left 2 hcard
  obtain ⟨d, hL, _⟩ := hY ∅ L hmixed hbudget
  rw [hL] at hell hm
  have hdell : d = ell.1 := (mem_affinePencil (Sum.inr d) ell).mp hell
  have hdm : d = m.1 := (mem_affinePencil (Sum.inr d) m).mp hm
  exact hdirections (hdell.symm.trans hdm)

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

structure PlaneLinearMap (F : Type*) [Field F] where
  xx : F
  xy : F
  yx : F
  yy : F
  determinant_ne_zero : xx * yy - xy * yx ≠ 0

namespace PlaneLinearMap

def determinant (M : PlaneLinearMap F) : F := M.xx * M.yy - M.xy * M.yx

def apply (M : PlaneLinearMap F) (p : Point F) : Point F :=
  (M.xx * p.1 + M.xy * p.2, M.yx * p.1 + M.yy * p.2)

def inverse (M : PlaneLinearMap F) (p : Point F) : Point F :=
  ((M.yy * p.1 - M.xy * p.2) / M.determinant,
    (M.xx * p.2 - M.yx * p.1) / M.determinant)

@[simp] theorem inverse_apply (M : PlaneLinearMap F) (p : Point F) :
    M.inverse (M.apply p) = p := by
  have hd : M.determinant ≠ 0 := M.determinant_ne_zero
  apply Prod.ext <;> dsimp [inverse, apply]
  · field_simp [hd]
    simp only [determinant]
    ring
  · field_simp [hd]
    simp only [determinant]
    ring

@[simp] theorem apply_inverse (M : PlaneLinearMap F) (p : Point F) :
    M.apply (M.inverse p) = p := by
  have hd : M.determinant ≠ 0 := M.determinant_ne_zero
  apply Prod.ext <;> dsimp [inverse, apply]
  · field_simp [hd]
    simp only [determinant]
    ring
  · field_simp [hd]
    simp only [determinant]
    ring

def toEquiv (M : PlaneLinearMap F) : Point F ≃ Point F where
  toFun := M.apply
  invFun := M.inverse
  left_inv := M.inverse_apply
  right_inv := M.apply_inverse

theorem apply_injective (M : PlaneLinearMap F) : Function.Injective M.apply :=
  M.toEquiv.injective

@[simp] theorem apply_zero (M : PlaneLinearMap F) : M.apply (0, 0) = (0, 0) := by
  simp [apply]

def diagonal (a : F) (ha : a ≠ 0) : PlaneLinearMap F where
  xx := 1
  xy := 0
  yx := 0
  yy := a
  determinant_ne_zero := by simpa using ha

@[simp] theorem diagonal_apply (a : F) (ha : a ≠ 0) (p : Point F) :
    (diagonal a ha).apply p = (p.1, a * p.2) := by
  simp [diagonal, apply]

def extra (u v : F) (huv : u ≠ v) : PlaneLinearMap F where
  xx := 1
  xy := 1
  yx := u
  yy := v
  determinant_ne_zero := by
    simpa only [one_mul] using sub_ne_zero.mpr huv.symm

@[simp] theorem extra_apply (u v : F) (huv : u ≠ v) (p : Point F) :
    (extra u v huv).apply p = (p.1 + p.2, u * p.1 + v * p.2) := by
  simp [extra, apply]

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k]

def mapPoint (σ : k →+* F) (p : Point k) : Point F := (σ p.1, σ p.2)

theorem mapPoint_injective (σ : k →+* F) : Function.Injective (mapPoint σ) := by
  intro p q hpq
  apply Prod.ext
  · exact σ.injective (congrArg Prod.fst hpq)
  · exact σ.injective (congrArg Prod.snd hpq)

def placedPoint (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (w : Point k) : Point F := b + M.apply (mapPoint σ w)

theorem placedPoint_injective (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) : Function.Injective (placedPoint σ M b) := by
  intro p q hpq
  apply mapPoint_injective σ
  apply M.apply_injective
  exact add_left_cancel hpq

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def directionVector : Direction F → Point F
  | none => (0, 1)
  | some a => (1, a)

theorem directionVector_kernel_iff (d e : Direction F) :
    projection d (directionVector e) = 0 ↔ d = e := let _ := instDecidableEqF; by
  cases d <;> cases e <;> simp [directionVector, projection, sub_eq_zero, eq_comm]

namespace PlaneLinearMap

def directionMap (M : PlaneLinearMap F) : Direction F → Direction F
  | none => if M.xy = 0 then none else some (M.yy / M.xy)
  | some a => if M.xx + M.xy * a = 0 then none
      else some ((M.yx + M.yy * a) / (M.xx + M.xy * a))

def projectionScale (M : PlaneLinearMap F) : Direction F → F
  | none => if M.xy = 0 then M.xx else -M.determinant / M.xy
  | some a => if M.xx + M.xy * a = 0 then M.xy
      else M.determinant / (M.xx + M.xy * a)

theorem projectionScale_ne_zero (M : PlaneLinearMap F) (d : Direction F) :
    M.projectionScale d ≠ 0 := by
  cases d with
  | none =>
      by_cases hxy : M.xy = 0
      · simp only [projectionScale, ite_eq_left hxy]
        intro hxx
        exact M.determinant_ne_zero (by simp [hxy, hxx])
      · simp only [projectionScale, ite_eq_right hxy]
        exact div_ne_zero (neg_ne_zero.mpr M.determinant_ne_zero) hxy
  | some a =>
      by_cases hA : M.xx + M.xy * a = 0
      · simp only [projectionScale, ite_eq_left hA]
        intro hxy
        have hxx : M.xx = 0 := by simpa only [hxy, zero_mul, add_zero] using hA
        exact M.determinant_ne_zero (by simp [hxy, hxx])
      · simp only [projectionScale, ite_eq_right hA]
        exact div_ne_zero M.determinant_ne_zero hA

theorem projection_directionMap_apply (M : PlaneLinearMap F)
    (d : Direction F) (p : Point F) :
    projection (M.directionMap d) (M.apply p) =
      M.projectionScale d * projection d p := by
  cases d with
  | none =>
      by_cases hxy : M.xy = 0
      · simp [directionMap, projectionScale, hxy, projection, apply]
      · simp only [directionMap, projectionScale, ite_eq_right hxy, projection, apply]
        field_simp [hxy]
        simp only [determinant]
        ring
  | some a =>
      by_cases hA : M.xx + M.xy * a = 0
      · have hxx : M.xx = -(M.xy * a) := eq_neg_of_add_eq_zero_left hA
        simp only [directionMap, projectionScale, ite_eq_left hA, projection, apply]
        rw [hxx]
        ring
      · simp only [directionMap, projectionScale, ite_eq_right hA, projection, apply]
        apply mul_right_cancel₀ hA
        calc
          (M.yx * p.1 + M.yy * p.2 -
              (M.yx + M.yy * a) / (M.xx + M.xy * a) *
                (M.xx * p.1 + M.xy * p.2)) * (M.xx + M.xy * a) =
              (M.yx * p.1 + M.yy * p.2) * (M.xx + M.xy * a) -
                ((M.yx + M.yy * a) / (M.xx + M.xy * a) * (M.xx + M.xy * a)) *
                  (M.xx * p.1 + M.xy * p.2) := by ring
          _ = (M.yx * p.1 + M.yy * p.2) * (M.xx + M.xy * a) -
                (M.yx + M.yy * a) * (M.xx * p.1 + M.xy * p.2) := by
              rw [div_mul_cancel₀ _ hA]
          _ = M.determinant * (p.2 - a * p.1) := by
              simp only [determinant]
              ring
          _ = (M.determinant / (M.xx + M.xy * a) * (M.xx + M.xy * a)) *
                (p.2 - a * p.1) := by rw [div_mul_cancel₀ _ hA]
          _ = (M.determinant / (M.xx + M.xy * a) * (p.2 - a * p.1)) *
                (M.xx + M.xy * a) := by ring

theorem projection_directionMap_apply_eq_iff (M : PlaneLinearMap F)
    (d : Direction F) (p q : Point F) :
    projection (M.directionMap d) (M.apply p) =
      projection (M.directionMap d) (M.apply q) ↔
      projection d p = projection d q := by
  rw [M.projection_directionMap_apply, M.projection_directionMap_apply]
  exact ⟨mul_left_cancel₀ (M.projectionScale_ne_zero d),
    congrArg (fun x => M.projectionScale d * x)⟩

theorem directionMap_injective (M : PlaneLinearMap F) :
    Function.Injective M.directionMap := by
  intro d e hde
  have hd : projection d (directionVector d) = 0 :=
    (directionVector_kernel_iff d d).2 rfl
  have hz : projection (M.directionMap e) (M.apply (directionVector d)) = 0 := by
    rw [← hde, M.projection_directionMap_apply, hd, mul_zero]
  rw [M.projection_directionMap_apply] at hz
  have he : projection e (directionVector d) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (M.projectionScale_ne_zero e)
  exact ((directionVector_kernel_iff e d).1 he).symm

theorem projection_directionMap_placed_eq_iff (M : PlaneLinearMap F)
    (b : Point F) (d : Direction F) (p q : Point F) :
    projection (M.directionMap d) (b + M.apply p) =
      projection (M.directionMap d) (b + M.apply q) ↔
      projection d p = projection d q := by
  change projection (M.directionMap d)
      (b.1 + (M.apply p).1, b.2 + (M.apply p).2) =
    projection (M.directionMap d)
      (b.1 + (M.apply q).1, b.2 + (M.apply q).2) ↔ _
  rw [projection_add, projection_add, add_left_cancel_iff]
  exact M.projection_directionMap_apply_eq_iff d p q

@[simp] theorem diagonal_directionMap_none (a : F) (ha : a ≠ 0) :
    (diagonal a ha).directionMap none = none := by
  simp [directionMap, diagonal]

@[simp] theorem diagonal_directionMap_some (a : F) (ha : a ≠ 0) (t : F) :
    (diagonal a ha).directionMap (some t) = some (a * t) := by
  simp [directionMap, diagonal]

@[simp] theorem extra_directionMap_none (u v : F) (huv : u ≠ v) :
    (extra u v huv).directionMap none = some v := by
  simp [directionMap, extra]

@[simp] theorem extra_directionMap_zero (u v : F) (huv : u ≠ v) :
    (extra u v huv).directionMap (some 0) = some u := by
  simp [directionMap, extra]

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k] [instDecidableEqk : DecidableEq k]

def mapDirection (σ : k →+* F) : Direction k → Direction F := Option.map σ

theorem mapDirection_injective (σ : k →+* F) : Function.Injective (mapDirection σ) := let _ := instDecidableEqF; let _ := instDecidableEqk; by
  intro d e hde
  cases d with
  | none =>
      cases e with
      | none => rfl
      | some b => cases hde
  | some a =>
      cases e with
      | none => cases hde
      | some b => exact congrArg Option.some (σ.injective (Option.some.inj hde))

theorem projection_mapDirection_mapPoint (σ : k →+* F) (d : Direction k)
    (p : Point k) :
    projection (mapDirection σ d) (mapPoint σ p) = σ (projection d p) := let _ := instDecidableEqF; let _ := instDecidableEqk; by
  cases d <;> simp [mapDirection, mapPoint, projection, map_sub, map_mul]

def placedDirection (σ : k →+* F) (M : PlaneLinearMap F) :
    Direction k → Direction F := fun d => M.directionMap (mapDirection σ d)

theorem placedDirection_injective (σ : k →+* F) (M : PlaneLinearMap F) :
    Function.Injective (placedDirection σ M) :=
  M.directionMap_injective.comp (mapDirection_injective σ)

theorem projection_placedPoint_eq_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (d : Direction k) (p q : Point k) :
    projection (placedDirection σ M d) (placedPoint σ M b p) =
      projection (placedDirection σ M d) (placedPoint σ M b q) ↔
      projection d p = projection d q := by
  unfold placedDirection placedPoint
  rw [M.projection_directionMap_placed_eq_iff,
    projection_mapDirection_mapPoint, projection_mapDirection_mapPoint]
  exact σ.injective.eq_iff

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k]

def lineAnchor (l : AffineLine k) : Point k :=
  match l.1 with
  | none => (l.2, 0)
  | some _ => (0, l.2)

@[simp] theorem projection_lineAnchor (l : AffineLine k) :
    projection l.1 (lineAnchor l) = l.2 := by
  obtain ⟨d, c⟩ := l
  cases d <;> simp [lineAnchor, projection]

@[simp] theorem incidence_lineAnchor (l : AffineLine k) :
    Incidence (lineAnchor l) l :=
  projection_lineAnchor l

variable {F : Type*} [Field F] [DecidableEq F] [instDecidableEqk : DecidableEq k]

def placedLine (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (l : AffineLine k) : AffineLine F :=
  lineThrough (placedDirection σ M l.1) (placedPoint σ M b (lineAnchor l))

@[simp] theorem placedLine_direction (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (l : AffineLine k) :
    (placedLine σ M b l).1 = placedDirection σ M l.1 := let _ := instDecidableEqk; rfl

theorem incidence_placedLine_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (p : Point k) (l : AffineLine k) :
    Incidence (placedPoint σ M b p) (placedLine σ M b l) ↔ Incidence p l := by
  change projection (placedDirection σ M l.1) (placedPoint σ M b p) =
      projection (placedDirection σ M l.1) (placedPoint σ M b (lineAnchor l)) ↔
    projection l.1 p = l.2
  rw [projection_placedPoint_eq_iff, projection_lineAnchor]

theorem placedLine_injective (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) : Function.Injective (placedLine σ M b) := by
  intro l m hlm
  have hdir : l.1 = m.1 :=
    placedDirection_injective σ M (congrArg Prod.fst hlm)
  have hinc : Incidence (lineAnchor l) m := by
    apply (incidence_placedLine_iff σ M b (lineAnchor l) m).mp
    rw [← hlm]
    exact (incidence_placedLine_iff σ M b (lineAnchor l) l).mpr
      (incidence_lineAnchor l)
  exact line_eq_of_direction_eq_of_incidence hdir (incidence_lineAnchor l) hinc

theorem eq_placedLine_of_direction_of_incidence
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (p : Point k) (d : Direction k) (ell : AffineLine F)
    (hdir : ell.1 = placedDirection σ M d)
    (hinc : Incidence (placedPoint σ M b p) ell) :
    ell = placedLine σ M b (d, projection d p) := by
  apply line_eq_of_direction_eq_of_incidence
  · exact hdir
  · exact hinc
  · exact (incidence_placedLine_iff σ M b p (d, projection d p)).mpr rfl

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [instFintypek : Fintype k]

def alteredDirections (σ : k →+* F) (M : PlaneLinearMap F) : Finset (Direction F) :=
  (Finset.univ.erase 0).image (fun t : k => placedDirection σ M (some t))

def axisDirections (σ : k →+* F) (M : PlaneLinearMap F) : Finset (Direction F) :=
  ({none, some 0} : Finset (Direction k)).image (placedDirection σ M)

theorem mem_alteredDirections_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction F) :
    d ∈ alteredDirections σ M ↔
      ∃ t : k, t ≠ 0 ∧ placedDirection σ M (some t) = d := by
  simp only [alteredDirections, Finset.mem_image, Finset.mem_erase,
    Finset.mem_univ, and_true]

theorem mem_axisDirections_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction F) :
    d ∈ axisDirections σ M ↔
      d = placedDirection σ M none ∨ d = placedDirection σ M (some 0) := let _ := instFintypek; by
  simp [axisDirections]

theorem placedDirection_mem_alteredDirections (σ : k →+* F) (M : PlaneLinearMap F)
    (t : k) (ht : t ≠ 0) :
    placedDirection σ M (some t) ∈ alteredDirections σ M :=
  (mem_alteredDirections_iff σ M _).mpr ⟨t, ht, rfl⟩

theorem disjoint_alteredDirections_axisDirections (σ : k →+* F)
    (M : PlaneLinearMap F) : Disjoint (alteredDirections σ M) (axisDirections σ M) := by
  apply Finset.disjoint_left.mpr
  intro d hd ha
  obtain ⟨t, ht, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
  rcases (mem_axisDirections_iff σ M _).mp ha with hnone | hzero
  · have h := placedDirection_injective σ M hnone
    cases h
  · exact ht (Option.some.inj (placedDirection_injective σ M hzero))

theorem placedDirection_axis_notMem_alteredDirections (σ : k →+* F)
    (M : PlaneLinearMap F) (d : Direction k) (haxis : d = none ∨ d = some 0) :
    placedDirection σ M d ∉ alteredDirections σ M := by
  have ha : placedDirection σ M d ∈ axisDirections σ M := by
    apply (mem_axisDirections_iff σ M _).mpr
    rcases haxis with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  intro hd
  exact Finset.disjoint_left.mp (disjoint_alteredDirections_axisDirections σ M) hd ha

theorem placedDirection_mem_altered_or_axis (σ : k →+* F) (M : PlaneLinearMap F)
    (d : Direction k) :
    placedDirection σ M d ∈ alteredDirections σ M ∪ axisDirections σ M := by
  cases d with
  | none =>
      exact Finset.mem_union_right _ ((mem_axisDirections_iff σ M _).mpr (Or.inl rfl))
  | some t =>
      by_cases ht : t = 0
      · subst t
        exact Finset.mem_union_right _ ((mem_axisDirections_iff σ M _).mpr (Or.inr rfl))
      · exact Finset.mem_union_left _ (placedDirection_mem_alteredDirections σ M t ht)

theorem card_alteredDirections (σ : k →+* F) (M : PlaneLinearMap F) :
    (alteredDirections σ M).card = Fintype.card k - 1 := by
  have hinj : Function.Injective (fun t : k => placedDirection σ M (some t)) := by
    intro t u h
    exact Option.some.inj (placedDirection_injective σ M h)
  unfold alteredDirections
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]

theorem existsUnique_alteredSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    ∃! t : k, t ≠ 0 ∧ placedDirection σ M (some t) = d.val := by
  obtain ⟨t, ht, htd⟩ := (mem_alteredDirections_iff σ M d.val).mp d.property
  refine ⟨t, ⟨ht, htd⟩, ?_⟩
  intro u hu
  exact Option.some.inj (placedDirection_injective σ M (hu.2.trans htd.symm))

noncomputable def alteredInverseSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) : k :=
  Classical.choose (existsUnique_alteredSlope σ M d).exists

theorem alteredInverseSlope_spec (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    alteredInverseSlope σ M d ≠ 0 ∧
      placedDirection σ M (some (alteredInverseSlope σ M d)) = d.val :=
  Classical.choose_spec (existsUnique_alteredSlope σ M d).exists

theorem placedDirection_inverseSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    placedDirection σ M (some (alteredInverseSlope σ M d)) = d.val :=
  (alteredInverseSlope_spec σ M d).2

theorem inverseSlope_placedDirection (σ : k →+* F) (M : PlaneLinearMap F)
    (t : k) (ht : t ≠ 0) :
    alteredInverseSlope σ M
      ⟨placedDirection σ M (some t), placedDirection_mem_alteredDirections σ M t ht⟩ = t := by
  apply Option.some.inj
  apply placedDirection_injective σ M
  exact placedDirection_inverseSlope σ M
    ⟨placedDirection σ M (some t), placedDirection_mem_alteredDirections σ M t ht⟩

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [instFintypeF : Fintype F] [DecidableEq k] [DecidableEq F]

def OriginalLineDensity (a : GadgetOutcome k) : Prop :=
  ∀ t : NonzeroSlope k, ∀ c : k, c ≠ a t →
    5 ≤ ((retainedPoints a).filter (fun p => Incidence p (some t.val, c))).card

def deletedLines (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) : Finset (AffineLine F) :=
  Finset.univ.filter (fun ell => ell.1 ∈ alteredDirections σ M ∧
    ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell)

@[simp] theorem mem_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ell : AffineLine F) :
    ell ∈ deletedLines σ M b a ↔ ell.1 ∈ alteredDirections σ M ∧
      ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell := by
  simp only [deletedLines, Finset.mem_filter, Finset.mem_univ, true_and]

theorem intercept_ne_omitted_of_mem_retained (a : GadgetOutcome k)
    (t : NonzeroSlope k) {p : Point k} {c : k}
    (hp : p ∈ retainedPoints a) (hpc : Incidence p (some t.val, c)) :
    c ≠ a t := by
  intro hc
  apply not_incidence_omittedLine a hp t
  simpa only [omittedLine, hc] using hpc

theorem deletedLines_direction_eq_image (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (t : NonzeroSlope k) :
    (deletedLines σ M b a).filter
        (fun ell => ell.1 = placedDirection σ M (some t.val)) =
      (Finset.univ.erase (a t)).image
        (fun c : k => placedLine σ M b (some t.val, c)) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hdel, hdir⟩ := Finset.mem_filter.mp hell
    obtain ⟨y, hy, hyell⟩ := ((mem_deletedLines σ M b a ell).mp hdel).2
    have hline : ell = placedLine σ M b
        (some t.val, projection (some t.val) y) :=
      eq_placedLine_of_direction_of_incidence σ M b y (some t.val) ell hdir hyell
    have hc : projection (some t.val) y ≠ a t :=
      intercept_ne_omitted_of_mem_retained a t hy rfl
    exact Finset.mem_image.mpr
      ⟨projection (some t.val) y, Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩,
        hline.symm⟩
  · intro hell
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hell
    have hpos : 0 < ((retainedPoints a).filter
        (fun p => Incidence p (some t.val, c))).card :=
      lt_of_lt_of_le (by decide : 0 < 5) (ha t c (Finset.mem_erase.mp hc).1)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    obtain ⟨hyret, hyline⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨(mem_deletedLines σ M b a _).mpr ?_, rfl⟩
    exact ⟨placedDirection_mem_alteredDirections σ M t.val t.property,
      y, hyret, (incidence_placedLine_iff σ M b y _).mpr hyline⟩

theorem card_deletedLines_direction (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (t : NonzeroSlope k) :
    ((deletedLines σ M b a).filter
      (fun ell => ell.1 = placedDirection σ M (some t.val))).card =
        Fintype.card k - 1 := by
  have hinj : Function.Injective
      (fun c : k => placedLine σ M b (some t.val, c)) := by
    intro c c' h
    exact congrArg Prod.snd (placedLine_injective σ M b h)
  rw [deletedLines_direction_eq_image σ M b a ha t,
    Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (Finset.mem_univ (a t)), Finset.card_univ]

theorem card_deletedLines_of_mem_alteredDirections (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (ha : OriginalLineDensity a) (d : Direction F)
    (hd : d ∈ alteredDirections σ M) :
    ((deletedLines σ M b a).filter (fun ell => ell.1 = d)).card =
      Fintype.card k - 1 := by
  obtain ⟨t, ht, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
  exact card_deletedLines_direction σ M b a ha ⟨t, ht⟩

theorem card_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (ha : OriginalLineDensity a) :
    (deletedLines σ M b a).card = (Fintype.card k - 1) ^ 2 := by
  calc
    (deletedLines σ M b a).card =
        ∑ d ∈ alteredDirections σ M,
          ((deletedLines σ M b a).filter (fun ell => ell.1 = d)).card :=
      Finset.card_eq_sum_card_fiberwise
        (fun ell hell => ((mem_deletedLines σ M b a ell).mp hell).1)
    _ = (alteredDirections σ M).card * (Fintype.card k - 1) :=
      Finset.sum_const_nat (fun d hd =>
        card_deletedLines_of_mem_alteredDirections σ M b a ha d hd)
    _ = (Fintype.card k - 1) ^ 2 := by rw [card_alteredDirections, pow_two]

theorem card_placedRetained_incident_placedLine (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (l : AffineLine k) :
    (((retainedPoints a).image (placedPoint σ M b)).filter
      (fun p => Incidence p (placedLine σ M b l))).card =
        ((retainedPoints a).filter (fun p => Incidence p l)).card := let _ := instFintypeF; by
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (placedPoint_injective σ M b)]
  congr 1
  ext p
  simp only [Finset.mem_filter, incidence_placedLine_iff]

theorem deletedLine_many_placedRetainedPoints (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (ha : OriginalLineDensity a) {ell : AffineLine F}
    (hell : ell ∈ deletedLines σ M b a) :
    5 ≤ (((retainedPoints a).image (placedPoint σ M b)).filter
      (fun p => Incidence p ell)).card := by
  obtain ⟨t, ht, htd⟩ := (mem_alteredDirections_iff σ M ell.1).mp
    ((mem_deletedLines σ M b a ell).mp hell).1
  have hfiber : ell ∈ (deletedLines σ M b a).filter
      (fun ell => ell.1 = placedDirection σ M (some t)) :=
    Finset.mem_filter.mpr ⟨hell, htd.symm⟩
  rw [deletedLines_direction_eq_image σ M b a ha ⟨t, ht⟩] at hfiber
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hfiber
  rw [card_placedRetained_incident_placedLine]
  exact ha ⟨t, ht⟩ c (Finset.mem_erase.mp hc).1

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

def GoodGadget (a : GadgetOutcome k) : Prop :=
  OriginalLineDensity a ∧
    (∀ ell : AffineLine k,
      Fintype.card k ≤ 8 * (transformedRetained a ∩ linePoints ell).card) ∧
    GadgetCoverProperty (transformedRetained a)

theorem gadgetConfig_survivors_ignoring_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (a : GadgetOutcome k) (ell : AffineLine k) :
    LineCover.survivors {linePoints ell} (gadgetConfig a) = transformedRetained a := by
  have hnot : linePoints ell ∉ LineCover.selected (gadgetConfig a) := by
    intro hmem
    exact selected_cubicShapes_ne_linePoints (gadgetConfig a) hcard hmem ell rfl
  calc
    _ = LineCover.survivors ∅ (gadgetConfig a) :=
      LineCover.survivors_insert_eq_of_not_selected hnot
    _ = transformedRetained a := gadgetConfig_survivors hcop a

theorem gadget_line_density_of_goodLineCover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (a : GadgetOutcome k)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a))
    (ell : AffineLine k) :
    Fintype.card k ≤ 8 * (transformedRetained a ∩ linePoints ell).card := by
  have h := hgood.1 ell
  rw [gadgetConfig_survivors_ignoring_line hcop hcard a ell] at h
  have hreal : (Fintype.card k : ℝ) ≤
      8 * ((transformedRetained a ∩ linePoints ell).card : ℝ) := by linarith
  exact_mod_cast hreal

theorem gadget_near_pencil_of_goodLineCover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (a : GadgetOutcome k)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a))
    (B : Finset (Point k)) (L : Finset (AffineLine k))
    (hcover : ∀ y ∈ transformedRetained a, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell)
    (hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card k) :
    ∃ p : ProjectivePoint k,
      99 * Fintype.card k ≤ 100 * (L ∩ affinePencil p).card := by
  have hL : L.card ≤ Fintype.card k := by omega
  have hB : B.card ≤ 2 * Fintype.card k := by omega
  have hmiss : (LineCover.survivors ∅ (gadgetConfig a) \ L.biUnion linePoints).card ≤
      2 * Fintype.card k := by
    rw [gadgetConfig_survivors hcop a]
    exact (Finset.card_le_card (missed_points_subset_of_mixed_cover
      (transformedRetained a) B L hcover)).trans hB
  obtain ⟨p, hp⟩ := hgood.2 L hL hmiss
  have heq : LineCover.coverPencil L p = L ∩ affinePencil p := by
    ext ell
    simp only [LineCover.mem_coverPencil, Finset.mem_inter, mem_affinePencil]
  rw [heq] at hp
  refine ⟨p, ?_⟩
  have hreal : (99 : ℝ) * Fintype.card k ≤
      100 * ((L ∩ affinePencil p).card : ℝ) := by linarith
  exact_mod_cast hreal

theorem goodGadget_of_events
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (hcard : 3 < Fintype.card k)
    (hlarge : 200 < 19 * Fintype.card k) (a : GadgetOutcome k)
    (horiginal : OriginalLineDensity a)
    (hgood : LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a)) :
    GoodGadget a := by
  have hlines := gadget_line_density_of_goodLineCover hcop hcard a hgood
  refine ⟨horiginal, hlines, ?_⟩
  exact gadgetCoverProperty_of_near_pencils (transformedRetained a) hlarge hlines
    (gadget_near_pencil_of_goodLineCover hcop a hgood)

theorem GoodGadget.retained_nonempty {a : GadgetOutcome k} (ha : GoodGadget a) :
    (retainedPoints a).Nonempty := by
  by_contra hn
  have hY : retainedPoints a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hT : transformedRetained a = ∅ := by simp [transformedRetained, hY]
  have hline := ha.2.1 (none, 0)
  rw [hT, Finset.empty_inter, Finset.card_empty, Nat.mul_zero] at hline
  exact (Nat.not_le_of_gt Fintype.card_pos) hline

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Exposure

open scoped BigOperators

variable {Omega : Type*} [instFintypeOmega : Fintype Omega]

def splitConfig (n : Nat) :
    (Fin (n + 1) → Omega) ≃ Omega × (Fin n → Omega) where
  toFun w := (w 0, fun i => w i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨x, tail⟩
    rfl

theorem cons_head_tail {n : Nat} (w : Fin (n + 1) → Omega) :
    Fin.cons (w 0) (fun i => w i.succ) = w := let _ := instFintypeOmega;
  (splitConfig n).left_inv w

def headMean {n : Nat} (mu : Fin (n + 1) → FiniteLaw Omega)
    (f : (Fin (n + 1) → Omega) → ℝ) (x : Omega) : ℝ :=
  (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
    (fun tail => f (Fin.cons x tail))

theorem expectation_pi_succ {n : Nat}
    (mu : Fin (n + 1) → FiniteLaw Omega)
    (f : (Fin (n + 1) → Omega) → ℝ) :
    (FiniteLaw.pi mu).expectation f =
      (mu 0).expectation (headMean mu f) := by
  classical
  change (∑ w, (∏ i, (mu i).weight (w i)) * f w) =
    ∑ x, (mu 0).weight x *
      (∑ tail : Fin n → Omega,
        (∏ i, (mu i.succ).weight (tail i)) * f (Fin.cons x tail))
  calc
    _ = ∑ p : Omega × (Fin n → Omega),
        ((mu 0).weight p.1 * ∏ i, (mu i.succ).weight (p.2 i)) *
          f (Fin.cons p.1 p.2) := by
      refine Fintype.sum_equiv (splitConfig n) _ _ ?_
      intro w
      change (∏ i, (mu i).weight (w i)) * f w =
        ((mu 0).weight (w 0) * ∏ i : Fin n, (mu i.succ).weight (w i.succ)) *
          f (Fin.cons (w 0) (fun i => w i.succ))
      rw [cons_head_tail, Fin.prod_univ_succ]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      ring

def ExposureBounds (M : ℝ) : (n : Nat) →
    (Fin n → FiniteLaw Omega) → ((Fin n → Omega) → ℝ) →
    (Fin n → ℝ) → Prop
  | 0, _, _, _ => True
  | n + 1, mu, f, v =>
      (∀ x, |headMean mu f x - (mu 0).expectation (headMean mu f)| ≤ M) ∧
      (mu 0).expectation
        (fun x => (headMean mu f x - (mu 0).expectation (headMean mu f)) ^ 2)
        ≤ v 0 ∧
      ∀ x, ExposureBounds M n (fun i => mu i.succ)
        (fun tail => f (Fin.cons x tail)) (fun i => v i.succ)

theorem mean_difference_bound {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f g : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a - g a| ≤ C) :
    |p.expectation f - p.expectation g| ≤ C := by
  have hlo : p.expectation (fun a => g a - C) ≤ p.expectation f := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).1
    linarith
  have hhi : p.expectation f ≤ p.expectation (fun a => g a + C) := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).2
    linarith
  rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const] at hlo
  rw [FiniteLaw.expectation_add, FiniteLaw.expectation_const] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem second_moment_le {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a| ≤ C) :
    p.expectation (fun a => (f a) ^ 2) ≤ C ^ 2 := by
  calc
    _ ≤ p.expectation (fun _ => C ^ 2) := by
      apply p.expectation_mono
      intro a
      rcases abs_le.mp (h a) with ⟨hl, hu⟩
      have hp : 0 ≤ (C - f a) * (C + f a) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    _ = C ^ 2 := p.expectation_const _

theorem update_cons_zero {n : Nat} (x y : Omega) (tail : Fin n → Omega) :
    Function.update
        (Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x tail) 0 y =
      Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) y tail :=
  Fin.update_cons_zero (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail y

theorem cons_update {n : Nat} (x y : Omega) (tail : Fin n → Omega) (i : Fin n) :
    Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x
        (Function.update tail i y) =
      Function.update
        (Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail) i.succ y :=
  Fin.cons_update (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail i y

theorem exposureBounds_of_coordinateBound (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hM : ∀ i, c i ≤ M) :
    ExposureBounds M n mu f (fun i => (c i) ^ 2) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hdiam (x y : Omega) :
        |headMean mu f x - headMean mu f y| ≤ c 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hcoord 0 (Fin.cons y tail) x
    have hcenter (x : Omega) :
        |headMean mu f x - (mu 0).expectation (headMean mu f)| ≤ c 0 := by
      have hh := mean_difference_bound (mu 0) (fun _ => headMean mu f x)
        (headMean mu f) (c 0) (hdiam x)
      simpa only [FiniteLaw.expectation_const] using hh
    refine ⟨fun x => (hcenter x).trans (hM 0), ?_, ?_⟩
    · exact second_moment_le (mu 0)
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
        (c 0) hcenter
    · intro x
      refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
        (fun i => c i.succ) ?_ (fun i => hM i.succ)
      intro i tail y
      simpa only [cons_update] using hcoord i.succ (Fin.cons x tail) y

end RyserCoveringCounterexample.Exposure

end OAI
end

section
namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

lemma expectation_mul_left_real {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    p.expectation (fun a => c * f a) = c * p.expectation f := by
  classical
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (le_abs_self (Real.exp x - 1 - x)).trans
    (Real.abs_exp_sub_one_sub_id_le hx)
  linarith

lemma expectation_exp_le_of_mean_zero {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (z : Ω → ℝ) (M v θ : ℝ)
    (hz : p.expectation z = 0)
    (hbound : ∀ a, |z a| ≤ M)
    (hsecond : p.expectation (fun a => (z a) ^ 2) ≤ v)
    (hθ : |θ| * M ≤ 1) :
    p.expectation (fun a => Real.exp (θ * z a)) ≤
      Real.exp (θ ^ 2 * v) := by
  classical
  have hpoint (a : Ω) :
      Real.exp (θ * z a) ≤ 1 + θ * z a + θ ^ 2 * (z a) ^ 2 := by
    have habs : |θ * z a| ≤ 1 := calc
      |θ * z a| = |θ| * |z a| := abs_mul _ _
      _ ≤ |θ| * M := mul_le_mul_of_nonneg_left (hbound a) (abs_nonneg θ)
      _ ≤ 1 := hθ
    have he := exp_le_one_add_add_sq habs
    nlinarith [he]
  have hlin :
      (∑ a, p.weight a * (θ * z a)) = θ * p.expectation z := by
    exact expectation_mul_left_real p θ z
  have hquad :
      (∑ a, p.weight a * (θ ^ 2 * (z a) ^ 2)) =
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
    exact expectation_mul_left_real p (θ ^ 2) (fun a => (z a) ^ 2)
  calc
    p.expectation (fun a => Real.exp (θ * z a)) ≤
        p.expectation (fun a => 1 + θ * z a + θ ^ 2 * (z a) ^ 2) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a)
    _ = 1 + θ * p.expectation z +
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      change (∑ a, p.weight a * (1 + θ * z a + θ ^ 2 * (z a) ^ 2)) = _
      simp only [mul_add, mul_one, Finset.sum_add_distrib]
      rw [p.total, hlin, hquad]
    _ = 1 + θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      rw [hz]
      ring
    _ ≤ 1 + θ ^ 2 * v :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond (sq_nonneg θ))
    _ ≤ Real.exp (θ ^ 2 * v) := by
      simpa only [add_comm] using Real.add_one_le_exp (θ ^ 2 * v)

lemma iterated_centered_mgf_le
    {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : A → FiniteLaw B)
    (f : A → B → ℝ) (head : A → ℝ)
    (center θ v V : ℝ)
    (hhead : p.expectation (fun a => Real.exp (θ * (head a - center))) ≤
      Real.exp (θ ^ 2 * v))
    (htail : ∀ a, (q a).expectation
        (fun b => Real.exp (θ * (f a b - head a))) ≤ Real.exp (θ ^ 2 * V)) :
    p.expectation (fun a => (q a).expectation
      (fun b => Real.exp (θ * (f a b - center)))) ≤
        Real.exp (θ ^ 2 * (v + V)) := by
  classical
  have hsplit (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) =
        Real.exp (θ * (head a - center)) *
          (q a).expectation (fun b => Real.exp (θ * (f a b - head a))) := by
    rw [← expectation_mul_left_real]
    congr 1
    funext b
    rw [← Real.exp_add]
    congr 1
    ring
  have hinner (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) ≤
        Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center)) := by
    rw [hsplit]
    have h := mul_le_mul_of_nonneg_left (htail a)
      (Real.exp_pos (θ * (head a - center))).le
    simpa only [mul_comm] using h
  calc
    p.expectation (fun a => (q a).expectation
        (fun b => Real.exp (θ * (f a b - center)))) ≤
        p.expectation (fun a =>
          Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center))) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hinner a) (p.nonneg a)
    _ = Real.exp (θ ^ 2 * V) *
        p.expectation (fun a => Real.exp (θ * (head a - center))) :=
      expectation_mul_left_real p _ _
    _ ≤ Real.exp (θ ^ 2 * V) * Real.exp (θ ^ 2 * v) :=
      mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * (v + V)) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma chernoff_upper {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ : ℝ) (hθ : 0 ≤ θ) :
    p.prob (fun a => u ≤ f a) ≤
      Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) := by
  classical
  unfold prob expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  by_cases huf : u ≤ f a
  · simp only [ite_eq_left huf]
    have he : 1 ≤ Real.exp (-θ * u) * Real.exp (θ * f a) := calc
      1 = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (-θ * u + θ * f a) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hθ (sub_nonneg.mpr huf)]
      _ = Real.exp (-θ * u) * Real.exp (θ * f a) := Real.exp_add _ _
    calc
      p.weight a = p.weight a * 1 := by ring
      _ ≤ p.weight a * (Real.exp (-θ * u) * Real.exp (θ * f a)) :=
        mul_le_mul_of_nonneg_left he (p.nonneg a)
      _ = Real.exp (-θ * u) * (p.weight a * Real.exp (θ * f a)) := by ring
  · simp only [ite_eq_right huf]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (p.nonneg a) (Real.exp_pos _).le)

lemma chernoff_upper_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ V : ℝ)
    (hθ : 0 ≤ θ)
    (hmgf : p.expectation (fun a => Real.exp (θ * f a)) ≤
      Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ f a) ≤ Real.exp (θ ^ 2 * V - θ * u) := by
  calc
    p.prob (fun a => u ≤ f a) ≤
        Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) :=
      chernoff_upper p f u θ hθ
    _ ≤ Real.exp (-θ * u) * Real.exp (θ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * V - θ * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma bernstein_scalar_optimization
    (M V u P : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / M →
      P ≤ Real.exp (t ^ 2 * V - t * u)) :
    P ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  by_cases hcut : u / (2 * V) ≤ 1 / M
  · have ht : 0 < u / (2 * V) :=
      div_pos hu (mul_pos (by norm_num) hV)
    have hexp :
        (u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u =
          -(1 / 4 : ℝ) * (u ^ 2 / V) := by
      field_simp [ne_of_gt hV]; ring
    calc
      P ≤ Real.exp ((u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u) :=
        h _ ht hcut
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        rw [hexp]
        nlinarith [min_le_left (u ^ 2 / V) (u / M)]
  · have hcross : 2 * V < u * M := by
      have ht : 1 / M < u / (2 * V) := lt_of_not_ge hcut
      have ht' :=
        (div_lt_div_iff₀ hM (mul_pos (by norm_num) hV)).mp ht
      simpa using ht'
    have hnum : V - u * M ≤ -(u * M) / 4 := by
      nlinarith [mul_pos hu hM]
    have hexp :
        (1 / M) ^ 2 * V - (1 / M) * u ≤
          -(1 / 4 : ℝ) * (u / M) := by
      calc
        (1 / M) ^ 2 * V - (1 / M) * u =
            (V - u * M) / M ^ 2 := by
          field_simp [ne_of_gt hM]
        _ ≤ (-(u * M) / 4) / M ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg M)
        _ = -(1 / 4 : ℝ) * (u / M) := by
          field_simp [ne_of_gt hM]
    calc
      P ≤ Real.exp ((1 / M) ^ 2 * V - (1 / M) * u) :=
        h _ (div_pos (by norm_num) hM) le_rfl
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        have hmin :
            -(1 / 4 : ℝ) * (u / M) ≤
              -(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M) := by
          nlinarith [min_le_right (u ^ 2 / V) (u / M)]
        exact hexp.trans hmin

lemma prob_abs_ge_le_add {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ) :
    p.prob (fun a => u ≤ |f a|) ≤
      p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  change (if u ≤ |f a| then p.weight a else 0) ≤
    (if u ≤ f a then p.weight a else 0) + (if u ≤ -f a then p.weight a else 0)
  by_cases hs : 0 ≤ f a
  · rw [abs_of_nonneg hs]
    split_ifs <;> linarith [p.nonneg a]
  · rw [abs_of_nonpos (le_of_not_ge hs)]
    split_ifs <;> linarith [p.nonneg a]

lemma bernstein_abs_tail_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hmgf : ∀ θ : ℝ, |θ| * M ≤ 1 →
      p.expectation (fun a => Real.exp (θ * f a)) ≤
        Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ |f a|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  have upper : p.prob (fun a => u ≤ f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    exact chernoff_upper_of_mgf p f u θ V hθ.le (hmgf θ hadm)
  have lower : p.prob (fun a => u ≤ -f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    have hadmneg : |-θ| * M ≤ 1 := by
      simpa only [abs_neg] using hadm
    have hneg : p.expectation (fun a => Real.exp (θ * (-f a))) ≤
        Real.exp (θ ^ 2 * V) := by
      simpa only [neg_mul, mul_neg, neg_sq] using hmgf (-θ) hadmneg
    exact chernoff_upper_of_mgf p (fun a => -f a) u θ V hθ.le hneg
  calc
    p.prob (fun a => u ≤ |f a|) ≤
        p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) :=
      prob_abs_ge_le_add p f u
    _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) +
        Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
      add_le_add upper lower
    _ = 2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by ring

end RyserCoveringCounterexample.FiniteLaw

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Concentration

open scoped BigOperators
open Exposure

variable {Omega : Type*} [Fintype Omega]

theorem exposure_mgf (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (theta : ℝ)
    (hb : ExposureBounds M n mu f v) (htheta : |theta| * M ≤ 1) :
    (FiniteLaw.pi mu).expectation
      (fun w => Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      ≤ Real.exp (theta ^ 2 * ∑ i, v i) := by
  classical
  induction n with
  | zero =>
    have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext w
      apply congrArg f
      funext i
      exact Fin.elim0 i
    rw [hf]
    simp [FiniteLaw.expectation_const]
  | succ n ih =>
    rcases hb with ⟨hbound, hsecond, hrec⟩
    have hzero : (mu 0).expectation
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f)) = 0 := by
      rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const, sub_self]
    have hhead := FiniteLaw.expectation_exp_le_of_mean_zero (mu 0)
      (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
      M (v 0) theta hzero hbound hsecond htheta
    have htail (x : Omega) :
        (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
          (fun w => Real.exp (theta * (f (Fin.cons x w) - headMean mu f x)))
          ≤ Real.exp (theta ^ 2 * ∑ i : Fin n, v i.succ) := by
      exact ih (fun i => mu i.succ) (fun w => f (Fin.cons x w))
        (fun i => v i.succ) (hrec x)
    calc
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (FiniteLaw.pi mu).expectation f)))) :=
        expectation_pi_succ (n := n) mu
          (fun w : Fin (n + 1) → Omega =>
            Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (mu 0).expectation (headMean mu f))))) := by
        rw [expectation_pi_succ mu f]
      _ ≤ Real.exp (theta ^ 2 * (v 0 + ∑ i : Fin n, v i.succ)) :=
        FiniteLaw.iterated_centered_mgf_le (mu 0)
          (fun _ => FiniteLaw.pi (fun i : Fin n => mu i.succ))
          (fun x w => f (Fin.cons x w)) (headMean mu f)
          ((mu 0).expectation (headMean mu f)) theta (v 0)
          (∑ i : Fin n, v i.succ) hhead htail
      _ = _ := by rw [Fin.sum_univ_succ]

theorem concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hb : ExposureBounds M n mu f v) (hv : (∑ i, v i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply FiniteLaw.bernstein_abs_tail_of_mgf (FiniteLaw.pi mu)
    (fun w => f w - (FiniteLaw.pi mu).expectation f) M V u hM hV hu
  intro theta htheta
  exact (exposure_mgf M n mu f v theta hb htheta).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv (sq_nonneg theta)))

theorem coordinate_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hcM : ∀ i, c i ≤ M) (hcV : (∑ i, (c i) ^ 2) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (c i) ^ 2) M V u hM hV hu
    (exposureBounds_of_coordinateBound M n mu f c hcoord hcM) hcV

end RyserCoveringCounterexample.Concentration

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable (I Ω : Type*) [Fintype I]

def finCoordinateEquiv : (Fin (Fintype.card I) → Ω) ≃ (I → Ω) where
  toFun w i := w (Fintype.equivFin I i)
  invFun a j := a ((Fintype.equivFin I).symm j)
  left_inv w := by
    funext j
    simp
  right_inv a := by
    funext i
    simp

theorem finCoordinateEquiv_update [DecidableEq I]
    (w : Fin (Fintype.card I) → Ω) (j : Fin (Fintype.card I)) (x : Ω) :
    finCoordinateEquiv I Ω (Function.update w j x) =
      Function.update (finCoordinateEquiv I Ω w) ((Fintype.equivFin I).symm j) x := by
  funext i
  change Function.update w j x (Fintype.equivFin I i) =
    Function.update (fun i => w (Fintype.equivFin I i)) ((Fintype.equivFin I).symm j) x i
  by_cases hi : i = (Fintype.equivFin I).symm j
  · subst i
    simp
  · have hij : Fintype.equivFin I i ≠ j := by
      intro h
      apply hi
      have h' := congrArg (Fintype.equivFin I).symm h
      simpa only [Equiv.symm_apply_apply] using h'
    simp [Function.update, hi, hij]

variable {I Ω} [DecidableEq I] [Fintype Ω] [Nonempty Ω]

theorem uniform_coordinate_concentration
    (f : (I → Ω) → ℝ) (c M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c)
    (hcM : c ≤ M) (hcV : (Fintype.card I : ℝ) * c ^ 2 ≤ V) :
    (FiniteLaw.uniform (I → Ω)).prob
        (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  have hcoord' : ∀ (j : Fin (Fintype.card I)) (w : Fin (Fintype.card I) → Ω) x,
      |f (finCoordinateEquiv I Ω (Function.update w j x)) -
        f (finCoordinateEquiv I Ω w)| ≤ c := by
    intro j w x
    rw [finCoordinateEquiv_update]
    exact hcoord _ _ _
  have h := Concentration.coordinate_concentration (Fintype.card I)
    (fun _ => FiniteLaw.uniform Ω) (fun w => f (finCoordinateEquiv I Ω w))
    (fun _ => c) M V u hM hV hu hcoord' (fun _ => hcM) (by simpa using hcV)
  have hmean :
      (FiniteLaw.pi (fun _ : Fin (Fintype.card I) => FiniteLaw.uniform Ω)).expectation
        (fun w => f (finCoordinateEquiv I Ω w)) =
      (FiniteLaw.uniform (I → Ω)).expectation f := by
    rw [FiniteLaw.pi_uniform]
    calc
      _ = ((FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).map
          (finCoordinateEquiv I Ω)).expectation f :=
        (FiniteLaw.expectation_map _ _ _).symm
      _ = _ := by rw [FiniteLaw.map_uniform_equiv]
  rw [hmean, FiniteLaw.pi_uniform] at h
  have hprob :
      (FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).prob
        (fun w => u ≤ |f (finCoordinateEquiv I Ω w) -
          (FiniteLaw.uniform (I → Ω)).expectation f|) =
      (FiniteLaw.uniform (I → Ω)).prob
        (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) := by
    calc
      _ = ((FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).map
          (finCoordinateEquiv I Ω)).prob
          (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) :=
        (FiniteLaw.prob_map _ _ _).symm
      _ = _ := by rw [FiniteLaw.map_uniform_equiv]
  rw [hprob] at h
  exact h

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

def originalLineSurvivors (a : GadgetOutcome k) (d : NonzeroSlope k) (z : k) :
    Finset (Point k) :=
  (linePoints (some d.val, z)).filter
    (fun p => ∀ e : NonzeroSlope k, e ≠ d → ¬ Incidence p (omittedLine a e))

def originalLineCount (a : GadgetOutcome k) (d : NonzeroSlope k) (z : k) : ℝ :=
  (originalLineSurvivors a d z).card

@[simp] theorem mem_originalLineSurvivors (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (p : Point k) :
    p ∈ originalLineSurvivors a d z ↔
      Incidence p (some d.val, z) ∧
        ∀ e : NonzeroSlope k, e ≠ d → ¬ Incidence p (omittedLine a e) := by
  simp only [originalLineSurvivors, Finset.mem_filter, mem_linePoints]

theorem originalLineSurvivors_eq_retained_filter (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (hz : z ≠ a d) :
    originalLineSurvivors a d z =
      (retainedPoints a).filter (fun p => Incidence p (some d.val, z)) := by
  ext p
  simp only [mem_originalLineSurvivors, Finset.mem_filter, mem_retainedPoints]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨?_, hp⟩
    intro e
    by_cases hed : e = d
    · subst e
      intro he
      change projection (some d.val) p = z at hp
      change projection (some d.val) p = a d at he
      exact hz (hp.symm.trans he)
    · exact havoid e hed
  · rintro ⟨havoid, hp⟩
    exact ⟨hp, fun e _ => havoid e⟩

theorem originalLineCount_eq_retained_filter_card (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (hz : z ≠ a d) :
    originalLineCount a d z =
      ((retainedPoints a).filter (fun p => Incidence p (some d.val, z))).card := by
  rw [originalLineCount, originalLineSurvivors_eq_retained_filter a d z hz]

theorem originalLineSurvivors_update_same (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z x : k) :
    originalLineSurvivors (Function.update a d x) d z = originalLineSurvivors a d z := by
  ext p
  simp only [mem_originalLineSurvivors]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro e hed
    simpa only [omittedLine, Function.update_of_ne hed] using havoid e hed
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro e hed
    simpa only [omittedLine, Function.update_of_ne hed] using havoid e hed

private theorem originalLineSurvivors_card_le_add_one_of_agree_off
    (a b : GadgetOutcome k) (d : NonzeroSlope k) (z : k) (i : NonzeroSlope k)
    (hid : i ≠ d) (hagree : ∀ e, e ≠ i → a e = b e) :
    (originalLineSurvivors a d z).card ≤ (originalLineSurvivors b d z).card + 1 := by
  have hlines : (some d.val, z) ≠ omittedLine b i := by
    intro h
    apply hid
    apply Subtype.ext
    exact (Option.some.inj (congrArg Prod.fst h)).symm
  have hinter :
      (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_inter.mp hp
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_inter.mp hq
    exact eq_of_common_incidence_of_ne_lines hlines
      ((mem_linePoints _ _).mp hp₁) ((mem_linePoints _ _).mp hp₂)
      ((mem_linePoints _ _).mp hq₁) ((mem_linePoints _ _).mp hq₂)
  have hsub : originalLineSurvivors a d z ⊆
      originalLineSurvivors b d z ∪
        (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)) := by
    intro p hp
    by_cases hb : p ∈ originalLineSurvivors b d z
    · exact Finset.mem_union_left _ hb
    · apply Finset.mem_union_right
      have hp' := (mem_originalLineSurvivors a d z p).mp hp
      refine Finset.mem_inter.mpr ⟨(mem_linePoints _ _).mpr hp'.1, ?_⟩
      apply (mem_linePoints _ _).mpr
      by_contra hnot
      apply hb
      apply (mem_originalLineSurvivors b d z p).mpr
      refine ⟨hp'.1, ?_⟩
      intro e hed
      by_cases hei : e = i
      · subst e
        exact hnot
      · change ¬ Incidence p (some e.val, b e)
        rw [← hagree e hei]
        exact hp'.2 e hed
  calc
    (originalLineSurvivors a d z).card ≤
        (originalLineSurvivors b d z ∪
          (linePoints (some d.val, z) ∩ linePoints (omittedLine b i))).card :=
      Finset.card_le_card hsub
    _ ≤ (originalLineSurvivors b d z).card +
        (linePoints (some d.val, z) ∩ linePoints (omittedLine b i)).card :=
      Finset.card_union_le _ _
    _ ≤ (originalLineSurvivors b d z).card + 1 := Nat.add_le_add_left hinter _

theorem originalLineCount_update_abs_le (a : GadgetOutcome k)
    (d : NonzeroSlope k) (z : k) (i : NonzeroSlope k) (x : k) :
    |originalLineCount (Function.update a i x) d z - originalLineCount a d z| ≤ 2 := by
  by_cases hid : i = d
  · subst i
    simp only [originalLineCount, originalLineSurvivors_update_same, sub_self, abs_zero]
    norm_num
  · have hforward := originalLineSurvivors_card_le_add_one_of_agree_off
      (Function.update a i x) a d z i hid (by
        intro e hei
        exact Function.update_of_ne hei x a)
    have hreverse := originalLineSurvivors_card_le_add_one_of_agree_off
      a (Function.update a i x) d z i hid (by
        intro e hei
        exact (Function.update_of_ne hei x a).symm)
    have hforwardR : originalLineCount (Function.update a i x) d z ≤
        originalLineCount a d z + 1 := by
      unfold originalLineCount
      exact_mod_cast hforward
    have hreverseR : originalLineCount a d z ≤
        originalLineCount (Function.update a i x) d z + 1 := by
      unfold originalLineCount
      exact_mod_cast hreverse
    apply abs_le.mpr
    constructor <;> linarith

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

private theorem expectation_finset_sum
    {Ω ι : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expectation (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, μ.expectation (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, FiniteLaw.expectation_const]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, FiniteLaw.expectation_add, ih]

theorem card_nonzeroSlope :
    Fintype.card (NonzeroSlope k) = Fintype.card k - 1 := by
  change Fintype.card {e : k // ¬e = 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem prob_originalPoint_survival (d : NonzeroSlope k) (w : Point k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ∀ e, e ≠ d → ¬Incidence w (omittedLine a e)) =
      (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 2) := by
  classical
  have hsingle (e : NonzeroSlope k) :
      (FiniteLaw.uniform k).prob
          (fun z : k => Incidence w (some e.val, z)) =
        1 / (Fintype.card k : ℝ) := by
    rw [FiniteLaw.prob]
    rw [Finset.sum_eq_single_of_mem
      (projection (some e.val) w) (Finset.mem_univ _)]
    · simp [Incidence, FiniteLaw.uniform, one_div]
    · intro b _ hb
      apply ite_eq_right
      intro h
      exact hb (show projection (some e.val) w = b from h).symm
  have hcoord (e : NonzeroSlope k) :
      (FiniteLaw.uniform k).prob
          (fun z : k => e ≠ d → ¬Incidence w (some e.val, z)) =
        if e = d then 1 else 1 - 1 / (Fintype.card k : ℝ) := by
    by_cases he : e = d
    · simp [he]
    · simp only [ne_eq, he, not_false_eq_true, true_implies, ite_false]
      rw [FiniteLaw.prob_compl, hsingle e]
  change
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ∀ e, e ≠ d → ¬Incidence w (some e.val, a e)) = _
  rw [FiniteLaw.prob_pi
    (A := fun _ : NonzeroSlope k => k)
    (fun _ : NonzeroSlope k => FiniteLaw.uniform k)
    (fun (e : NonzeroSlope k) (b : k) =>
      e ≠ d → ¬Incidence w (some e.val, b))]
  simp_rw [hcoord]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ,
    card_nonzeroSlope]
  simp only [Nat.sub_sub]

theorem expectation_originalLineCount (d : NonzeroSlope k) (z : k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).expectation
        (fun a => originalLineCount a d z) =
      (Fintype.card k : ℝ) *
        (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 2) := by
  classical
  have hcount (a : GadgetOutcome k) :
      originalLineCount a d z =
        ∑ w ∈ linePoints (some d.val, z),
          if ∀ e : NonzeroSlope k, e ≠ d → ¬Incidence w (omittedLine a e)
          then (1 : ℝ) else 0 := by
    simp only [originalLineCount, originalLineSurvivors, Finset.sum_boole]
  calc
    _ = ∑ w ∈ linePoints (some d.val, z),
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).expectation
          (fun a => if ∀ e : NonzeroSlope k,
              e ≠ d → ¬Incidence w (omittedLine a e)
            then (1 : ℝ) else 0) := by
      simpa only [← hcount] using
        (expectation_finset_sum
          (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k))
          (linePoints (some d.val, z))
          (fun (w : Point k) (a : GadgetOutcome k) =>
            if ∀ e : NonzeroSlope k, e ≠ d → ¬Incidence w (omittedLine a e)
            then (1 : ℝ) else 0))
    _ = ∑ w ∈ linePoints (some d.val, z),
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
          (fun a => ∀ e, e ≠ d → ¬Incidence w (omittedLine a e)) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [FiniteLaw.prob_eq_expectation]
      apply congrArg (FiniteLaw.expectation
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)))
      funext a
      by_cases h : ∀ e : NonzeroSlope k,
          e ≠ d → ¬Incidence w (omittedLine a e)
      · simp
      · simp
    _ = _ := by
      simp only [prob_originalPoint_survival, Finset.sum_const,
        nsmul_eq_mul, card_linePoints]

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem tendsto_rpow_mul_exp_neg_rpow_atTop (r : ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => q ^ r * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (r / a) c hc).comp (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hq, mul_div_cancel₀ r ha.ne']

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

open Filter Topology

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem prob_originalLineCount_lt_five (hq : 2048 ≤ Fintype.card k)
    (d : NonzeroSlope k) (z : k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => originalLineCount a d z < 5) ≤
      Real.exp (-(Fintype.card k : ℝ) / 2048) := by
  classical
  let q : ℝ := Fintype.card k
  have hqR : 2048 ≤ q := by
    dsimp only [q]
    exact_mod_cast hq
  have hq0 : 0 < q := by linarith
  have hcoordinates : (Fintype.card (NonzeroSlope k) : ℝ) ≤ q := by
    dsimp only [q]
    exact_mod_cast Fintype.card_le_of_injective
      (fun d : NonzeroSlope k => d.val) Subtype.val_injective
  have hmean : q / 4 ≤
      (FiniteLaw.uniform (GadgetOutcome k)).expectation (fun a => originalLineCount a d z) := by
    have hm := LineCover.quarter_mul_le_survival_mean (Fintype.card k) (by omega)
    rw [← expectation_originalLineCount d z, FiniteLaw.pi_uniform] at hm
    exact hm
  have htail := uniform_coordinate_concentration
    (fun a : GadgetOutcome k => originalLineCount a d z)
    2 2 (4 * q) (q / 8) (by norm_num) (by positivity) (by positivity)
    (fun i a x => originalLineCount_update_abs_le a d z i x)
    (by norm_num) (by nlinarith)
  have hratio : (q / 8) ^ 2 / (4 * q) = q / 256 := by
    field_simp [hq0.ne']; ring
  have hmin : min ((q / 8) ^ 2 / (4 * q)) ((q / 8) / 2) = q / 256 := by
    rw [hratio]
    apply min_eq_left
    linarith
  rw [hmin] at htail
  have hexponent : -(1 / 4 : ℝ) * (q / 256) = -q / 1024 := by ring
  rw [hexponent] at htail
  have hbad :
      (FiniteLaw.uniform (GadgetOutcome k)).prob (fun a => originalLineCount a d z < 5) ≤
      (FiniteLaw.uniform (GadgetOutcome k)).prob
        (fun a => q / 8 ≤ |originalLineCount a d z -
          (FiniteLaw.uniform (GadgetOutcome k)).expectation
            (fun a => originalLineCount a d z)|) := by
    apply FiniteLaw.prob_mono
    intro a ha
    have habs := neg_le_abs (originalLineCount a d z -
      (FiniteLaw.uniform (GadgetOutcome k)).expectation (fun a => originalLineCount a d z))
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp (q / 2048) := by
    have he := Real.add_one_le_exp (q / 2048)
    linarith
  rw [FiniteLaw.pi_uniform]
  change _ ≤ Real.exp (-q / 2048)
  calc
    _ ≤ 2 * Real.exp (-q / 1024) := hbad.trans htail
    _ ≤ Real.exp (q / 2048) * Real.exp (-q / 1024) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-q / 2048) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem not_originalLineDensity_imp_exists_small_count (a : GadgetOutcome k)
    (ha : ¬ OriginalLineDensity a) :
    ∃ j : NonzeroSlope k × k, originalLineCount a j.1 j.2 < 5 := by
  classical
  simp only [OriginalLineDensity, not_forall, not_le] at ha
  obtain ⟨d, z, hz, hcard⟩ := ha
  refine ⟨(d, z), ?_⟩
  rw [originalLineCount_eq_retained_filter_card a d z hz]
  exact_mod_cast hcard

theorem prob_not_originalLineDensity_le (hq : 2048 ≤ Fintype.card k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ¬ OriginalLineDensity a) ≤
      (Fintype.card k : ℝ) ^ 2 * Real.exp (-(Fintype.card k : ℝ) / 2048) := by
  classical
  let μ := FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)
  have htests : (Fintype.card (NonzeroSlope k × k) : ℝ) ≤ (Fintype.card k : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul]
    have hc : (Fintype.card (NonzeroSlope k) : ℝ) ≤ (Fintype.card k : ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective
        (fun d : NonzeroSlope k => d.val) Subtype.val_injective
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Fintype.card k))
  calc
    _ ≤ μ.prob (fun a => ∃ j : NonzeroSlope k × k, originalLineCount a j.1 j.2 < 5) :=
      μ.prob_mono not_originalLineDensity_imp_exists_small_count
    _ ≤ ∑ j : NonzeroSlope k × k,
        μ.prob (fun a => originalLineCount a j.1 j.2 < 5) :=
      μ.prob_exists_le _
    _ ≤ ∑ _j : NonzeroSlope k × k, Real.exp (-(Fintype.card k : ℝ) / 2048) := by
      apply Finset.sum_le_sum
      intro j _
      exact prob_originalLineCount_lt_five hq j.1 j.2
    _ = (Fintype.card (NonzeroSlope k × k) : ℝ) *
        Real.exp (-(Fintype.card k : ℝ) / 2048) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right htests (Real.exp_pos _).le

theorem prob_originalLineDensity_ge (hq : 2048 ≤ Fintype.card k) :
    1 - (Fintype.card k : ℝ) ^ 2 * Real.exp (-(Fintype.card k : ℝ) / 2048) ≤
      (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        OriginalLineDensity := by
  have h := prob_not_originalLineDensity_le (k := k) hq
  rw [FiniteLaw.prob_compl] at h
  linarith

theorem tendsto_originalDensity_failure_atTop :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 2048))
      atTop (𝓝 0) := by
  have h : Tendsto (fun q : ℝ => q ^ 2 * Real.exp (-q / 2048)) atTop (𝓝 0) := by
    have h' := LineCover.tendsto_rpow_mul_exp_neg_rpow_atTop
      (2 : ℝ) (a := 1) (c := 1 / 2048) (by norm_num) (by norm_num)
    simpa [Real.rpow_natCast, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  exact h.comp tendsto_natCast_atTop_atTop

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

private theorem exists_mem_mod_three_eq_two_of_prod
    (L : List ℕ) (hL : L.prod % 3 = 2) :
    ∃ p ∈ L, p % 3 = 2 := by
  induction L with
  | nil => simp at hL
  | cons a L ih =>
      by_cases ha : a % 3 = 2
      · exact ⟨a, List.mem_cons_self, ha⟩
      · have hmod : a % 3 = 0 ∨ a % 3 = 1 := by
          have := Nat.mod_lt a (by decide : 0 < 3)
          omega
        rcases hmod with ha0 | ha1
        · simp only [List.prod_cons, Nat.mul_mod, ha0, zero_mul, Nat.zero_mod] at hL
          contradiction
        · have htail : L.prod % 3 = 2 := by
            simpa only [List.prod_cons, Nat.mul_mod, ha1, one_mul, Nat.mod_mod] using hL
          obtain ⟨p, hp, hpmod⟩ := ih htail
          exact ⟨p, List.mem_cons_of_mem a hp, hpmod⟩

theorem exists_prime_dvd_mod_three_eq_two {n : ℕ} (hn : n % 3 = 2) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 3 = 2 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, hp, hpmod⟩ :=
    exists_mem_mod_three_eq_two_of_prod n.primeFactorsList
      (by simpa only [Nat.prod_primeFactorsList hn0] using hn)
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp,
    Nat.dvd_of_mem_primeFactorsList hp, hpmod⟩

theorem exists_prime_gt_mod_three_eq_two (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ p % 3 = 2 := by
  let N := 3 * B.factorial - 1
  have hfacpos := Nat.factorial_pos B
  have hsucc : N + 1 = 3 * B.factorial := by
    dsimp [N]
    exact Nat.sub_add_cancel (by omega)
  have hNmod : N % 3 = 2 := by omega
  obtain ⟨p, hp, hpN, hpmod⟩ := exists_prime_dvd_mod_three_eq_two hNmod
  refine ⟨p, ?_, hp, hpmod⟩
  by_contra hnot
  have hpB : p ≤ B := Nat.le_of_not_gt hnot
  have hpfac : p ∣ B.factorial := Nat.dvd_factorial hp.pos hpB
  have hpprod : p ∣ 3 * B.factorial := dvd_mul_of_dvd_right hpfac 3
  have hsub : 3 * B.factorial - N = 1 := by omega
  have hpone : p ∣ 1 := by
    have h := Nat.dvd_sub hpprod hpN
    simpa only [hsub] using h
  have hple := Nat.le_of_dvd (by decide : 0 < 1) hpone
  have hptwo := hp.two_le
  omega

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

theorem extensionField_card (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Fintype.card (ExtensionField p n) = p ^ n := by
  simpa only [Nat.card_eq_fintype_card] using GaloisField.card p n hn

noncomputable def primeEmbedding (p n : ℕ) [Fact p.Prime] :
    ZMod p →+* ExtensionField p n := algebraMap _ _

theorem primeEmbedding_injective (p n : ℕ) [Fact p.Prime] :
    Function.Injective (primeEmbedding p n) :=
  (primeEmbedding p n).injective

@[simp] theorem primeEmbedding_eq_iff (p n : ℕ) [Fact p.Prime] (a b : ZMod p) :
    primeEmbedding p n a = primeEmbedding p n b ↔ a = b :=
  (primeEmbedding_injective p n).eq_iff

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F] [Fintype F]

theorem subfield_card_lt_of_ne_top (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S < Fintype.card F := by
  apply Fintype.card_lt_of_injective_not_surjective
    (fun x : S => (x : F)) Subtype.val_injective
  intro hsurj
  apply hS
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := hsurj x
  exact hy ▸ y.property

variable {p n : ℕ} [CharP F p]

theorem subfield_eq_top_of_card_eq_char (hp : p.Prime)
    (hcard : Fintype.card F = p) (S : Subfield F) : S = ⊤ := by
  classical
  let : Fintype S := Fintype.ofFinite S
  by_contra hS
  obtain ⟨m, _, hm⟩ := FiniteField.card S p
  have hpS : p ≤ Fintype.card S := by
    rw [hm]
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hp.pos m.property : p ^ 1 ≤ p ^ (m : ℕ))
  have hlt := subfield_card_lt_of_ne_top S hS
  rw [hcard] at hlt
  exact (not_lt_of_ge hpS) hlt

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

theorem primeField_subfield_eq_top (p : ℕ) [Fact p.Prime]
    (S : Subfield (ZMod p)) : S = ⊤ :=
  subfield_eq_top_of_card_eq_char (Fact.out : p.Prime) (ZMod.card p) S

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

universe u

alias uniform_linecover_probability := uniform_linecover_probability_oddExt

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open Filter Topology
noncomputable section

namespace RyserCoveringCounterexample.Construction

theorem exists_threshold_goodGadget :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ hp : p.Prime, p % 3 = 2 →
      5 < p ∧
        (letI : Fact p.Prime := ⟨hp⟩
         ∃ a : GadgetOutcome (ZMod p), GoodGadget a) := by
  classical
  obtain ⟨Q, hQ⟩ := LineCover.uniform_linecover_probability
    3 (1 / 4) (1 / 100) (by norm_num) (by norm_num) (by norm_num)
    (1 / 4) (by norm_num)
  have hsmall : ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 2048) < 1 / 4 :=
    (tendsto_order.mp tendsto_originalDensity_failure_atTop).2 _ (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨Q + N + 2048, ?_⟩
  intro p hpbound hp hpmod
  have hp5 : 5 < p := by omega
  have hpQ : Q ≤ p := by omega
  have hpN : N ≤ p := by omega
  have hp2048 : 2048 ≤ p := by omega
  refine ⟨hp5, ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  have hcard : 3 < Fintype.card (ZMod p) := by simpa using (show 3 < p by omega)
  have hcop : Nat.Coprime 3 (Fintype.card (ZMod p) - 1) :=
    coprime_three_zmod_card_sub_one hpmod
  have hsub : Incidence.SmallProperSubfields (ZMod p) := by
    intro M hM
    exact (hM (primeField_subfield_eq_top p M)).elim
  have hline := hQ (ZMod p) (by simpa using hpQ) hsub
    (cubicDeletionProcess hcop hcard)
  change 1 - (1 / 4 : ℝ) ≤
    (FiniteLaw.pi (gadgetTrials (k := ZMod p))).prob
      (LineCover.GoodLineCover (1 / 4) (1 / 100)) at hline
  rw [← gadgetLaw_map_config, FiniteLaw.prob_map] at hline
  have horiginal := prob_originalLineDensity_ge (k := ZMod p)
    (by simpa using hp2048)
  change 1 - (Fintype.card (ZMod p) : ℝ) ^ 2 *
      Real.exp (-(Fintype.card (ZMod p) : ℝ) / 2048) ≤
    (gadgetLaw (ZMod p)).prob OriginalLineDensity at horiginal
  have hfailure : (Fintype.card (ZMod p) : ℝ) ^ 2 *
      Real.exp (-(Fintype.card (ZMod p) : ℝ) / 2048) < 1 / 4 := by
    simpa using hN p hpN
  have hex : ∃ a : GadgetOutcome (ZMod p), OriginalLineDensity a ∧
      LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a) := by
    by_contra hnot
    have himp : ∀ a : GadgetOutcome (ZMod p), OriginalLineDensity a →
        ¬ LineCover.GoodLineCover (1 / 4) (1 / 100) (gadgetConfig a) := by
      intro a ha hgood
      exact hnot ⟨a, ha, hgood⟩
    have hmono := (gadgetLaw (ZMod p)).prob_mono himp
    rw [FiniteLaw.prob_compl] at hmono
    linarith
  obtain ⟨a, ha, hgood⟩ := hex
  refine ⟨a, goodGadget_of_events hcop hcard ?_ a ha hgood⟩
  simpa using (show 200 < 19 * p by omega)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

theorem three_mul_le_of_dvd_odd {d n : ℕ} (hn : Odd n) (hd : d ∣ n)
    (hne : d ≠ n) : 3 * d ≤ n := by
  obtain ⟨a, ha⟩ := hn
  obtain ⟨q, hq⟩ := hd
  have hq3 : 3 ≤ q := by
    by_contra h
    have hc : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hc with h0 | h1 | h2
    · subst q
      simp only [Nat.mul_zero] at hq
      omega
    · subst q
      simp only [Nat.mul_one] at hq
      omega
    · subst q
      simp only [Nat.mul_two] at hq
      omega
  calc
    3 * d = d * 3 := Nat.mul_comm _ _
    _ ≤ d * q := Nat.mul_le_mul_left d hq3
    _ = n := hq.symm

variable {F : Type*} [Field F] [Fintype F]
variable {p n : ℕ} [CharP F p]

theorem subfield_degree_data_of_odd (hp : p.Prime) (hn : Odd n)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ 3 * d ≤ n ∧ Fintype.card S = p ^ d := by
  obtain ⟨m, _, hm⟩ := FiniteField.card S p
  have hpow : p ^ n = p ^ ((m : ℕ) * Module.finrank S F) := by
    calc
      p ^ n = Fintype.card F := hcard.symm
      _ = Fintype.card S ^ Module.finrank S F :=
        Module.card_eq_pow_finrank (K := S) (V := F)
      _ = (p ^ (m : ℕ)) ^ Module.finrank S F := by rw [hm]
      _ = p ^ ((m : ℕ) * Module.finrank S F) :=
        (pow_mul p (m : ℕ) (Module.finrank S F)).symm
  have hdegree : n = (m : ℕ) * Module.finrank S F :=
    Nat.pow_right_injective hp.one_lt hpow
  have hdiv : (m : ℕ) ∣ n := ⟨Module.finrank S F, hdegree⟩
  have hne : (m : ℕ) ≠ n := by
    intro he
    have hlt := subfield_card_lt_of_ne_top S hS
    have hsame : Fintype.card S = Fintype.card F := by rw [hm, he, hcard]
    exact (ne_of_lt hlt) hsame
  exact ⟨m, m.property, hdiv, three_mul_le_of_dvd_odd hn hdiv hne, hm⟩

theorem subfield_card_cube_le_of_odd_degree (hp : p.Prime) (hn : Odd n)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S ^ 3 ≤ Fintype.card F := by
  obtain ⟨d, _, _, hd, hSd⟩ := subfield_degree_data_of_odd hp hn hcard S hS
  rw [hSd, hcard, ← pow_mul]
  exact Nat.pow_le_pow_right hp.pos (by simpa only [Nat.mul_comm] using hd)

theorem subfield_natCard_cube_le_of_odd_degree (hp : p.Prime) (hn : Odd n)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ Fintype.card F := by
  classical
  let : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using
    subfield_card_cube_le_of_odd_degree hp hn hcard S hS

theorem extensionField_properSubfield_cube_le_of_odd (p n : ℕ) [Fact p.Prime]
    (hn : Odd n) (_hn3 : 2 < n) (S : Subfield (ExtensionField p n)) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ Fintype.card (ExtensionField p n) := by
  have hn0 : n ≠ 0 := by obtain ⟨a, ha⟩ := hn; omega
  exact subfield_natCard_cube_le_of_odd_degree (Fact.out : p.Prime) hn
    (extensionField_card p n hn0) S hS

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

variable {V : Type*} [DecidableEq V]

def NonemptyEdges (H : Hypergraph V) : Prop := ∀ e ∈ H, e.Nonempty

def IsMatching (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ (M : Set (Finset V)).Pairwise Disjoint

end RyserCoveringCounterexample

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

variable {V : Type*} [instDecidableEqV : DecidableEq V] {H : Hypergraph V}

theorem NonemptyEdges.isCover_biUnion (hH : NonemptyEdges H) :
    IsCover H (H.biUnion id) := by
  intro e he
  obtain ⟨v, hve⟩ := hH e he
  exact ⟨v, Finset.mem_biUnion.mpr ⟨e, he, hve⟩, hve⟩

theorem NonemptyEdges.exists_cover (hH : NonemptyEdges H) :
    ∃ C : Finset V, IsCover H C :=
  ⟨H.biUnion id, hH.isCover_biUnion⟩

theorem IsCover.coverNumber_le {C : Finset V} (hC : IsCover H C) :
    coverNumber H ≤ C.card := let _ := instDecidableEqV;
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_minimum_cover_of_exists (hH : ∃ C : Finset V, IsCover H C) :
    ∃ C : Finset V, IsCover H C ∧ C.card = coverNumber H := let _ := instDecidableEqV; by
  apply Nat.sInf_mem (s := coverCardinalities H)
  obtain ⟨C, hC⟩ := hH
  exact ⟨C.card, C, hC, rfl⟩

theorem le_coverNumber_of_exists (hH : ∃ C : Finset V, IsCover H C) (k : ℕ)
    (hk : ∀ C : Finset V, IsCover H C → k ≤ C.card) : k ≤ coverNumber H := by
  obtain ⟨C, hC, hcard⟩ := exists_minimum_cover_of_exists hH
  rw [← hcard]
  exact hk C hC

theorem le_coverNumber (hH : NonemptyEdges H) (k : ℕ)
    (hk : ∀ C : Finset V, IsCover H C → k ≤ C.card) : k ≤ coverNumber H :=
  le_coverNumber_of_exists hH.exists_cover k hk

@[simp] theorem coverNumber_empty : coverNumber (∅ : Hypergraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (show IsCover (∅ : Hypergraph V) ∅ from by simp [IsCover]).coverNumber_le

theorem Intersecting.isCover_edge (hI : Intersecting H) (hH : NonemptyEdges H)
    {e : Finset V} (he : e ∈ H) : IsCover H e := by
  intro f hf
  by_cases hef : e = f
  · subst f
    obtain ⟨v, hv⟩ := hH e he
    exact ⟨v, hv, hv⟩
  · obtain ⟨v, hv⟩ := hI e he f hf hef
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

theorem coverNumber_le_edge_card (hI : Intersecting H) (hH : NonemptyEdges H)
    {e : Finset V} (he : e ∈ H) : coverNumber H ≤ e.card :=
  (hI.isCover_edge hH he).coverNumber_le

theorem coverNumber_eq_rank_of_no_small_cover {r : ℕ} (hr : 0 < r)
    (hU : Uniform r H) (hne : H.Nonempty) (hI : Intersecting H)
    (hsmall : ∀ C : Finset V, C.card ≤ r - 1 → ¬ IsCover H C) :
    coverNumber H = r := by
  have hH : NonemptyEdges H := by
    intro e he
    apply Finset.card_pos.mp
    rw [hU e he]
    exact hr
  apply le_antisymm
  · obtain ⟨e, he⟩ := hne
    exact (coverNumber_le_edge_card hI hH he).trans_eq (hU e he)
  · apply le_coverNumber hH r
    intro C hC
    by_contra hlt
    exact hsmall C (Nat.le_sub_one_of_lt (lt_of_not_ge hlt)) hC

end RyserCoveringCounterexample

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

variable {V : Type*} [instDecidableEqV : DecidableEq V]

@[simp] theorem mem_matchings {H M : Hypergraph V} :
    M ∈ matchings H ↔ IsMatching H M := let _ := instDecidableEqV; by
  classical
  simp only [matchings, Finset.mem_filter, Finset.mem_powerset, IsMatching]

theorem isMatching_singleton {H : Hypergraph V} {e : Finset V} (he : e ∈ H) :
    IsMatching H {e} := let _ := instDecidableEqV; by
  constructor
  · exact Finset.singleton_subset_iff.mpr he
  · simp

theorem IsMatching.card_le_matchingNumber {H M : Hypergraph V}
    (hM : IsMatching H M) : M.card ≤ matchingNumber H := by
  exact Finset.le_sup (mem_matchings.mpr hM)

theorem matchingNumber_le_iff {H : Hypergraph V} (n : ℕ) :
    matchingNumber H ≤ n ↔ ∀ M, IsMatching H M → M.card ≤ n := by
  change (matchings H).sup Finset.card ≤ n ↔ _
  rw [Finset.sup_le_iff]
  constructor
  · intro h M hM
    exact h M (mem_matchings.mpr hM)
  · intro h M hM
    exact h M (mem_matchings.mp hM)

theorem matchingNumber_le {H : Hypergraph V} {n : ℕ}
    (h : ∀ M, IsMatching H M → M.card ≤ n) : matchingNumber H ≤ n :=
  (matchingNumber_le_iff n).mpr h

theorem matchingNumber_le_card (H : Hypergraph V) : matchingNumber H ≤ H.card := by
  apply matchingNumber_le
  intro M hM
  exact Finset.card_le_card hM.1

@[simp] theorem matchingNumber_empty : matchingNumber (∅ : Hypergraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [Finset.card_empty] using matchingNumber_le_card (∅ : Hypergraph V)

theorem one_le_matchingNumber_of_nonempty {H : Hypergraph V} (hH : H.Nonempty) :
    1 ≤ matchingNumber H := by
  obtain ⟨e, he⟩ := hH
  simpa only [Finset.card_singleton] using
    (isMatching_singleton he).card_le_matchingNumber

theorem IsMatching.card_le_one_of_intersecting {H M : Hypergraph V}
    (hM : IsMatching H M) (hH : Intersecting H) : M.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  obtain ⟨v, hv⟩ := hH e (hM.1 he) f (hM.1 hf) hne
  exact (Finset.disjoint_left.mp (hM.2 he hf hne))
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2

theorem matchingNumber_eq_one_of_nonempty_intersecting {H : Hypergraph V}
    (hH : H.Nonempty) (hI : Intersecting H) : matchingNumber H = 1 := by
  apply le_antisymm
  · apply matchingNumber_le
    intro M hM
    exact hM.card_le_one_of_intersecting hI
  · exact one_le_matchingNumber_of_nonempty hH

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

variable {V I J : Type*} [instDecidableEqV : DecidableEq V]

theorem PartiteUniform.edgePart_bijective {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) {e : Finset V} (he : e ∈ H) :
    Function.Bijective (fun v : ↥e => part v.val) := let _ := instDecidableEqV; by
  constructor
  · intro v w hvw
    apply Subtype.ext
    exact (hpart e he (part v.val)).unique
      ⟨v.property, rfl⟩ ⟨w.property, hvw.symm⟩
  · intro i
    obtain ⟨v, hve, hvi⟩ := (hpart e he i).exists
    exact ⟨⟨v, hve⟩, hvi⟩

theorem PartiteUniform.edge_card [Fintype I] {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) {e : Finset V} (he : e ∈ H) :
    e.card = Fintype.card I := by
  exact (Fintype.card_coe e).symm.trans
    (Fintype.card_of_bijective (hpart.edgePart_bijective he))

theorem RPartiteUniform.uniform {r : ℕ} {H : Hypergraph V}
    (hpart : RPartiteUniform r H) : Uniform r H := by
  obtain ⟨part, hpart⟩ := hpart
  intro e he
  simpa only [Fintype.card_fin] using hpart.edge_card he

theorem Uniform.nonemptyEdges {r : ℕ} {H : Hypergraph V}
    (huniform : Uniform r H) (hr : 0 < r) : NonemptyEdges H := let _ := instDecidableEqV; by
  intro e he
  apply Finset.card_pos.mp
  rw [huniform e he]
  exact hr

theorem RPartiteUniform.nonemptyEdges {r : ℕ} {H : Hypergraph V}
    (hpart : RPartiteUniform r H) (hr : 0 < r) : NonemptyEdges H :=
  hpart.uniform.nonemptyEdges hr

theorem PartiteUniform.relabel {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) (f : I ≃ J) :
    PartiteUniform (f ∘ part) H := let _ := instDecidableEqV; by
  intro e he j
  obtain ⟨v, hv, huniq⟩ := hpart e he (f.symm j)
  refine ⟨v, ⟨hv.1, ?_⟩, ?_⟩
  · change f (part v) = j
    rw [hv.2, f.apply_symm_apply]
  · intro w hw
    apply huniq w
    refine ⟨hw.1, ?_⟩
    exact f.injective (hw.2.trans (f.apply_symm_apply j).symm)

theorem PartiteUniform.rPartiteUniform [Fintype I] {part : V → I}
    {H : Hypergraph V} (hpart : PartiteUniform part H) :
    RPartiteUniform (Fintype.card I) H := by
  refine ⟨(Fintype.equivFin I) ∘ part, ?_⟩
  exact hpart.relabel (Fintype.equivFin I)

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

def CounterexampleRank (r : ℕ) : Prop :=
  ∃ (V : Type) (fin : Fintype V) (dec : DecidableEq V),
    letI : Fintype V := fin
    letI : DecidableEq V := dec
    ∃ H : Hypergraph V,
      0 < r ∧ H.Nonempty ∧ RPartiteUniform r H ∧ Intersecting H ∧
        (∃ C : Finset V, IsCover H C) ∧ matchingNumber H = 1 ∧ coverNumber H = r

theorem counterexampleRank_of_no_small_cover {V : Type} [Fintype V] [DecidableEq V]
    {r : ℕ} {H : Hypergraph V} (hr : 0 < r) (hne : H.Nonempty)
    (hpart : RPartiteUniform r H) (hI : Intersecting H)
    (hsmall : ∀ C : Finset V, C.card ≤ r - 1 → ¬ IsCover H C) :
    CounterexampleRank r := by
  refine ⟨V, inferInstance, inferInstance, H, hr, hne, hpart, hI, ?_, ?_, ?_⟩
  · exact (hpart.nonemptyEdges hr).exists_cover
  · exact matchingNumber_eq_one_of_nonempty_intersecting hne hI
  · exact coverNumber_eq_rank_of_no_small_cover hr hpart.uniform hne hI hsmall

theorem infinite_counterexampleRanks_of_unbounded
    (h : ∀ b : ℕ, ∃ r : ℕ, b < r ∧ CounterexampleRank r) :
    Set.Infinite {r : ℕ | CounterexampleRank r} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨r, hbr, hr⟩ := h b
  exact (not_le_of_gt hbr) (hb hr)

end RyserCoveringCounterexample

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def ambientShapes (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Finset (Point F)) := Finset.univ.image linePoints

theorem linePoints_mem_ambientShapes (l : AffineLine F) :
    linePoints l ∈ ambientShapes F := Finset.mem_image_of_mem _ (Finset.mem_univ l)

theorem ambient_linePoints_injective : Function.Injective (linePoints (F := F)) := by
  intro l m h
  by_contra hlm
  have hbound := card_linePoints_inter_le_one hlm
  rw [h, Finset.inter_self, card_linePoints] at hbound
  exact (Fintype.one_lt_card : 1 < Fintype.card F).not_ge hbound

theorem ambientShapes_count_le {D : ℕ} (hD : 2 ≤ D) :
    (ambientShapes F).card ≤ D * Fintype.card F ^ D := by
  have hq : 1 ≤ Fintype.card F := Nat.succ_le_of_lt Fintype.card_pos
  have hpow : Fintype.card F ^ 2 ≤ Fintype.card F ^ D :=
    pow_le_pow_right₀ hq hD
  calc
    (ambientShapes F).card ≤ Fintype.card (AffineLine F) :=
      (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = Fintype.card F * (Fintype.card F + 1) := card_affineLine
    _ ≤ 2 * Fintype.card F ^ 2 := by nlinarith
    _ ≤ D * Fintype.card F ^ D := Nat.mul_le_mul hD hpow

theorem ambientShapes_size_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset (Point F)) (hS : S ∈ ambientShapes F) :
    S.card ≤ D * Fintype.card F := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hS
  rw [card_linePoints]
  simpa only [one_mul] using Nat.mul_le_mul_right (Fintype.card F) hD

theorem ambientShapes_sparse {D : ℕ} (hD : 1 ≤ D) :
    LineCover.SparseShapes (ambientShapes F) D := by
  intro S hS l hne
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hS
  have hml : m ≠ l := fun h => hne (congrArg linePoints h)
  exact (card_linePoints_inter_le_one hml).trans hD

def ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F)) (hB : B.card ≤ D) :
    LineCover.Outcome (ambientShapes F) D :=
  ⟨B.image (fun l => (⟨linePoints l, linePoints_mem_ambientShapes l⟩ :
      ↥(ambientShapes F))), Finset.card_image_le.trans hB⟩

theorem mem_deleted_ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) (ignore : Finset (Finset (Point F))) (x : Point F) :
    x ∈ LineCover.deleted ignore (ambientLineOutcome B hB) ↔
      ∃ l ∈ B, linePoints l ∉ ignore ∧ Incidence x l := by
  rw [LineCover.mem_deleted]
  constructor
  · rintro ⟨S, hS, hignore, hx⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨l, hl, hignore, (mem_linePoints x l).mp hx⟩
  · rintro ⟨l, hl, hignore, hx⟩
    exact ⟨⟨linePoints l, linePoints_mem_ambientShapes l⟩,
      Finset.mem_image_of_mem _ hl, hignore, (mem_linePoints x l).mpr hx⟩

theorem ambientLineOutcome_lists_line {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) (l : AffineLine F) :
    (∃ S ∈ (ambientLineOutcome B hB).val, S.val = linePoints l) ↔ l ∈ B := by
  constructor
  · rintro ⟨S, hS, heq⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
    exact ambient_linePoints_injective heq ▸ hm
  · intro hl
    exact ⟨⟨linePoints l, linePoints_mem_ambientShapes l⟩,
      Finset.mem_image_of_mem _ hl, rfl⟩

theorem deleted_empty_ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) :
    LineCover.deleted ∅ (ambientLineOutcome B hB) = B.biUnion linePoints := by
  ext x
  simp only [mem_deleted_ambientLineOutcome, Finset.notMem_empty, not_false_eq_true, true_and,
    Finset.mem_biUnion, mem_linePoints]

def ambientDeletionConstant (s K : ℕ) : ℕ :=
  2 + (s - 1) ^ 2 + 2 * K + 2 * K * (s - 1)

theorem ambientDeletionConstant_two_le (s K : ℕ) :
    2 ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_lines_le (s K : ℕ) :
    (s - 1) ^ 2 ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_trials_le (s K : ℕ) :
    2 * K ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_lineRate_le (s K : ℕ) :
    2 * K * (s - 1) ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F] {n K : ℕ}

theorem projection_sub_eq (d : Direction F) (p q : Point F) :
    projection d (p - q) = projection d p - projection d q := let _ := instDecidableEqF; by
  exact RyserCoveringCounterexample.projection_sub d p q

def Feasible (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) : Prop :=
  ∀ e ∈ T, ¬ Conflict data i e.1 b (pool e)

@[simp] theorem feasible_empty (data : Data F n) (pool : Pool F n K)
    (i : Fin n) (b : Point F) : Feasible data ∅ pool i b := by
  simp [Feasible]

section Finite
variable [Fintype F]

noncomputable def feasibleSet (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) : Finset (Point F) := by
  classical
  exact Finset.univ.filter (Feasible data T pool i)

@[simp] theorem mem_feasibleSet (data : Data F n) (T : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) :
    b ∈ feasibleSet data T pool i ↔ Feasible data T pool i b := by
  classical
  simp only [feasibleSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem feasibleSet_empty (data : Data F n) (pool : Pool F n K)
    (i : Fin n) : feasibleSet data ∅ pool i = Finset.univ := by
  classical
  ext b
  simp

end Finite
end RyserCoveringCounterexample.Selection

end OAI
end

section
namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

theorem uniform_prob_projection (d : Direction F) (c : F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => projection d b = c) =
      1 / (Fintype.card F : ℝ) := by
  classical
  rw [FiniteLaw.uniform_prob]
  calc
    _ = ((linePoints (d, c)).card : ℝ) / (Fintype.card (Point F) : ℝ) := by
      apply congrArg (fun T : Finset (Point F) =>
        (T.card : ℝ) / (Fintype.card (Point F) : ℝ))
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_linePoints, Incidence]
    _ = _ := by
      rw [card_linePoints, card_point, Nat.cast_pow]
      have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

end RyserCoveringCounterexample.Selection

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

def shiftAffineLine (b : Point F) (l : AffineLine F) : AffineLine F :=
  (l.1, l.2 + projection l.1 b)

@[simp] theorem shiftAffineLine_direction (b : Point F) (l : AffineLine F) :
    (shiftAffineLine b l).1 = l.1 := rfl

@[simp] theorem shiftAffineLine_offset (b : Point F) (l : AffineLine F) :
    (shiftAffineLine b l).2 = l.2 + projection l.1 b := rfl

@[simp] theorem shiftAffineLine_zero (l : AffineLine F) : shiftAffineLine 0 l = l := by
  obtain ⟨d, c⟩ := l
  cases d <;> simp [shiftAffineLine, projection]

theorem incidence_shiftAffineLine_iff (b x : Point F) (l : AffineLine F) :
    Incidence x (shiftAffineLine b l) ↔ Incidence (x - b) l := by
  change projection l.1 x = l.2 + projection l.1 b ↔ projection l.1 (x - b) = l.2
  have hproj : projection l.1 (x - b) = projection l.1 x - projection l.1 b :=
    projection_sub l.1 x b
  rw [hproj, sub_eq_iff_eq_add]

section Finite

variable [Fintype F] [DecidableEq F]

def ambientLineUnion (B : Finset (AffineLine F)) : Finset (Point F) :=
  B.biUnion linePoints

@[simp] theorem mem_ambientLineUnion (B : Finset (AffineLine F)) (x : Point F) :
    x ∈ ambientLineUnion B ↔ ∃ l ∈ B, Incidence x l := by
  simp only [ambientLineUnion, Finset.mem_biUnion, mem_linePoints]

theorem mem_ambientLineUnion_shift (B : Finset (AffineLine F)) (b x : Point F) :
    x ∈ ambientLineUnion (B.image (shiftAffineLine b)) ↔ x - b ∈ ambientLineUnion B := by
  rw [mem_ambientLineUnion, mem_ambientLineUnion]
  constructor
  · rintro ⟨l, hl, hxl⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨m, hm, (incidence_shiftAffineLine_iff b x m).mp hxl⟩
  · rintro ⟨l, hl, hxl⟩
    exact ⟨shiftAffineLine b l, Finset.mem_image.mpr ⟨l, hl, rfl⟩,
      (incidence_shiftAffineLine_iff b x l).mpr hxl⟩

theorem card_ambientLineUnion_le (B : Finset (AffineLine F)) :
    (ambientLineUnion B).card ≤ B.card * Fintype.card F :=
  Finset.card_biUnion_le_card_mul B linePoints (Fintype.card F)
    (fun l _ => (card_linePoints l).le)

theorem uniform_prob_mem_ambientLineUnion_shift (B : Finset (AffineLine F)) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob
        (fun b => x ∈ ambientLineUnion (B.image (shiftAffineLine b))) =
      ((ambientLineUnion B).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  have hinj : Function.Injective (fun y : Point F => x - y) := by
    intro y z hyz
    have h := congrArg (fun w : Point F => x - w) hyz
    simpa only [sub_sub_cancel] using h
  rw [FiniteLaw.uniform_prob]
  calc
    _ = (((ambientLineUnion B).image (fun y => x - y)).card : ℝ) /
        (Fintype.card (Point F) : ℝ) := by
      apply congrArg (fun T : Finset (Point F) =>
        (T.card : ℝ) / (Fintype.card (Point F) : ℝ))
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_ambientLineUnion_shift]
      constructor
      · intro hb
        exact Finset.mem_image.mpr ⟨x - b, hb, sub_sub_cancel x b⟩
      · intro hb
        obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
        rw [← hyb, sub_sub_cancel]
        exact hy
    _ = _ := by
      rw [Finset.card_image_of_injective _ hinj, card_point, Nat.cast_pow]

theorem uniform_prob_mem_ambientLineUnion_shift_le (B : Finset (AffineLine F))
    (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob
        (fun b => x ∈ ambientLineUnion (B.image (shiftAffineLine b))) ≤
      (B.card : ℝ) / (Fintype.card F : ℝ) := by
  rw [uniform_prob_mem_ambientLineUnion_shift]
  have hcard : ((ambientLineUnion B).card : ℝ) ≤
      (B.card : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast card_ambientLineUnion_le B
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    ((ambientLineUnion B).card : ℝ) / (Fintype.card F : ℝ) ^ 2 ≤
        ((B.card : ℝ) * (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ = (B.card : ℝ) / (Fintype.card F : ℝ) := by
      field_simp [hq]

theorem uniform_prob_mem_image_shiftAffineLine_le (B : Finset (AffineLine F))
    (l : AffineLine F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => l ∈ B.image (shiftAffineLine b)) ≤
      ((B.filter (fun e => e.1 = l.1)).card : ℝ) / (Fintype.card F : ℝ) := by
  classical
  let T := B.filter (fun e => e.1 = l.1)
  have hP : (fun b => l ∈ B.image (shiftAffineLine b)) =
      (fun b => ∃ e : ↥T, projection l.1 b = l.2 - e.val.2) := by
    funext b
    apply propext
    constructor
    · intro hb
      obtain ⟨e, heB, heq⟩ := Finset.mem_image.mp hb
      have hdir := congrArg Prod.fst heq
      change e.1 = l.1 at hdir
      have hoff := congrArg Prod.snd heq
      change e.2 + projection e.1 b = l.2 at hoff
      have hproj : projection l.1 b = l.2 - e.2 := by
        rw [← hdir]
        apply (eq_sub_iff_add_eq).2
        exact (add_comm _ _).trans hoff
      exact ⟨⟨e, Finset.mem_filter.mpr ⟨heB, hdir⟩⟩, hproj⟩
    · rintro ⟨e, heq⟩
      have hdir : e.val.1 = l.1 := (Finset.mem_filter.mp e.property).2
      refine Finset.mem_image.mpr ⟨e.val, (Finset.mem_filter.mp e.property).1, ?_⟩
      apply Prod.ext
      · exact hdir
      · change e.val.2 + projection e.val.1 b = l.2
        rw [hdir, heq]
        ring
  rw [hP]
  calc
    _ ≤ ∑ e : ↥T, (FiniteLaw.uniform (Point F)).prob
        (fun b => projection l.1 b = l.2 - e.val.2) := FiniteLaw.prob_exists_le _ _
    _ = ∑ _e : ↥T, 1 / (Fintype.card F : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      exact Selection.uniform_prob_projection l.1 (l.2 - e.val.2)
    _ = ((B.filter (fun e => e.1 = l.1)).card : ℝ) / (Fintype.card F : ℝ) := by
      simp [T, div_eq_mul_inv]

end Finite

section Placed

variable {k : Type*} [Field k] [instFintypek : Fintype k] [instDecidableEqk : DecidableEq k]
variable [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem placedPoint_sub_shift (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (y : Point k) :
    placedPoint σ M b y - b = placedPoint σ M 0 y := let _ := instFintypek; let _ := instDecidableEqk; let _ := instFintypeF; let _ := instDecidableEqF; by
  simp only [placedPoint, add_sub_cancel_left, zero_add]

theorem mem_deletedLines_shift (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (l : AffineLine F) :
    shiftAffineLine b l ∈ deletedLines σ M b a ↔ l ∈ deletedLines σ M 0 a := by
  simp only [mem_deletedLines, shiftAffineLine_direction, incidence_shiftAffineLine_iff,
    placedPoint_sub_shift]

theorem deletedLines_eq_image_shiftAffineLine (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) :
    deletedLines σ M b a = (deletedLines σ M 0 a).image (shiftAffineLine b) := by
  ext l
  constructor
  · intro hl
    let m : AffineLine F := (l.1, l.2 - projection l.1 b)
    have hm : shiftAffineLine b m = l := by
      apply Prod.ext
      · rfl
      · exact sub_add_cancel _ _
    refine Finset.mem_image.mpr ⟨m, ?_, hm⟩
    apply (mem_deletedLines_shift σ M b a m).mp
    rw [hm]
    exact hl
  · intro hl
    obtain ⟨m, hm, hml⟩ := Finset.mem_image.mp hl
    rw [← hml]
    exact (mem_deletedLines_shift σ M b a m).mpr hm

theorem uniform_prob_mem_deletedLines_union (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      ((ambientLineUnion (deletedLines σ M 0 a)).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  have hP : (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      (fun b => x ∈ ambientLineUnion ((deletedLines σ M 0 a).image (shiftAffineLine b))) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_ambientLineUnion_shift (deletedLines σ M 0 a) x

theorem uniform_prob_mem_deletedLines_union_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (x : Point F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) ≤
      ((deletedLines σ M 0 a).card : ℝ) / (Fintype.card F : ℝ) := by
  have hP : (fun b => x ∈ ambientLineUnion (deletedLines σ M b a)) =
      (fun b => x ∈ ambientLineUnion ((deletedLines σ M 0 a).image (shiftAffineLine b))) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_ambientLineUnion_shift_le (deletedLines σ M 0 a) x

theorem uniform_prob_mem_deletedLines_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (l : AffineLine F) :
    (FiniteLaw.uniform (Point F)).prob (fun b => l ∈ deletedLines σ M b a) ≤
      (((deletedLines σ M 0 a).filter (fun e => e.1 = l.1)).card : ℝ) /
        (Fintype.card F : ℝ) := by
  have hP : (fun b => l ∈ deletedLines σ M b a) =
      (fun b => l ∈ (deletedLines σ M 0 a).image (shiftAffineLine b)) := by
    funext b
    rw [deletedLines_eq_image_shiftAffineLine σ M b a]
  rw [hP]
  exact uniform_prob_mem_image_shiftAffineLine_le (deletedLines σ M 0 a) l

end Placed

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]

theorem embeddedUnits_injective (σ : k →+* F) : Function.Injective (embeddedUnits σ) :=
  Units.map_injective σ.injective

def unitCoset (σ : k →+* F) (a : Fˣ) : CosetIndex σ := QuotientGroup.mk a

def cosetRepresentative (σ : k →+* F) (c : CosetIndex σ) : Fˣ := by
  classical
  exact if c = 1 then 1 else c.out

@[simp] theorem cosetRepresentative_one (σ : k →+* F) :
    cosetRepresentative σ 1 = 1 := by
  classical
  simp [cosetRepresentative]

@[simp] theorem unitCoset_representative (σ : k →+* F) (c : CosetIndex σ) :
    unitCoset σ (cosetRepresentative σ c) = c := by
  classical
  by_cases hc : c = 1
  · subst c
    simp [cosetRepresentative, unitCoset]
  · simp only [cosetRepresentative, ite_eq_right hc, unitCoset]
    exact Quotient.out_eq' c

theorem unitCoset_eq_iff (σ : k →+* F) (a b : Fˣ) :
    unitCoset σ a = unitCoset σ b ↔
      ∃ u : kˣ, embeddedUnits σ u = a / b := by
  change (a : Fˣ ⧸ smallUnitSubgroup σ) = b ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  rfl

theorem exists_embeddedUnit_mul_representative (σ : k →+* F) (a : Fˣ) :
    ∃ u : kˣ, a = embeddedUnits σ u * cosetRepresentative σ (unitCoset σ a) := by
  have hc : unitCoset σ a =
      unitCoset σ (cosetRepresentative σ (unitCoset σ a)) := by simp
  obtain ⟨u, hu⟩ := (unitCoset_eq_iff σ _ _).mp hc
  refine ⟨u, ?_⟩
  rw [hu, div_mul_cancel]

abbrev ConfigurationGroup (σ : k →+* F) := Option (CosetIndex σ)

theorem natCard_smallUnitSubgroup (σ : k →+* F) :
    Nat.card (smallUnitSubgroup σ) = Nat.card k - 1 := by
  calc
    Nat.card (smallUnitSubgroup σ) = Nat.card kˣ :=
      (Nat.card_congr (MonoidHom.ofInjective (embeddedUnits_injective σ)).toEquiv).symm
    _ = Nat.card k - 1 := Nat.card_units k

theorem natCard_cosetIndex_mul (σ : k →+* F) :
    Nat.card (CosetIndex σ) * (Nat.card k - 1) = Nat.card F - 1 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (smallUnitSubgroup σ)
  rw [Nat.card_units, natCard_smallUnitSubgroup] at h
  exact h.symm

section Finite

variable [instFintypek : Fintype k] [Fintype F]

theorem card_cosetIndex_mul (σ : k →+* F) :
    Fintype.card (CosetIndex σ) * (Fintype.card k - 1) = Fintype.card F - 1 := by
  simpa only [Nat.card_eq_fintype_card] using natCard_cosetIndex_mul σ

theorem card_configurationGroup (σ : k →+* F) :
    Fintype.card (ConfigurationGroup σ) = Fintype.card (CosetIndex σ) + 1 := let _ := instFintypek;
  Fintype.card_option

end Finite

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [instFintypek : Fintype k]

def cosetPlacement (σ : k →+* F) (c : CosetIndex σ) : PlaneLinearMap F :=
  PlaneLinearMap.diagonal (cosetRepresentative σ c : F)
    (cosetRepresentative σ c).ne_zero

@[simp] theorem placedDirection_coset_none (σ : k →+* F) (c : CosetIndex σ) :
    placedDirection σ (cosetPlacement σ c) none = none := let _ := instDecidableEqk; let _ := instFintypek; by
  simp [placedDirection, mapDirection, cosetPlacement]

@[simp] theorem placedDirection_coset_some (σ : k →+* F) (c : CosetIndex σ)
    (t : k) :
    placedDirection σ (cosetPlacement σ c) (some t) =
      some ((cosetRepresentative σ c : F) * σ t) := let _ := instDecidableEqk; let _ := instFintypek; by
  simp [placedDirection, mapDirection, cosetPlacement]

theorem mem_coset_altered_iff (σ : k →+* F) (c : CosetIndex σ)
    (d : Direction F) :
    d ∈ alteredDirections σ (cosetPlacement σ c) ↔
      ∃ t : k, t ≠ 0 ∧ d = some ((cosetRepresentative σ c : F) * σ t) := by
  rw [mem_alteredDirections_iff]
  simp only [placedDirection_coset_some, eq_comm]

@[simp] theorem none_notMem_coset_altered (σ : k →+* F) (c : CosetIndex σ) :
    none ∉ alteredDirections σ (cosetPlacement σ c) := by
  simp [mem_coset_altered_iff]

@[simp] theorem zero_notMem_coset_altered (σ : k →+* F) (c : CosetIndex σ) :
    some 0 ∉ alteredDirections σ (cosetPlacement σ c) := by
  rintro hd
  obtain ⟨t, ht, heq⟩ := (mem_coset_altered_iff σ c _).mp hd
  have hz := Option.some.inj heq
  exact mul_ne_zero (cosetRepresentative σ c).ne_zero
    (fun hz' => ht (σ.injective (hz'.trans (map_zero σ).symm))) hz.symm

theorem unitCoset_mul_embedded (σ : k →+* F) (a : Fˣ) (u : kˣ) :
    unitCoset σ (a * embeddedUnits σ u) = unitCoset σ a := let _ := instDecidableEqk; let _ := instDecidableEqF; let _ := instFintypek; by
  apply (unitCoset_eq_iff σ _ _).mpr
  refine ⟨u, ?_⟩
  simp only [mul_div_cancel_left]

theorem some_unit_mem_coset_altered_iff (σ : k →+* F) (c : CosetIndex σ)
    (a : Fˣ) :
    some (a : F) ∈ alteredDirections σ (cosetPlacement σ c) ↔
      unitCoset σ a = c := by
  constructor
  · intro ha
    obtain ⟨t, ht, heq⟩ := (mem_coset_altered_iff σ c _).mp ha
    have hu : a = cosetRepresentative σ c * embeddedUnits σ (Units.mk0 t ht) := by
      apply Units.ext
      simpa [embeddedUnits] using Option.some.inj heq
    rw [hu, unitCoset_mul_embedded, unitCoset_representative]
  · intro ha
    obtain ⟨u, hu⟩ := exists_embeddedUnit_mul_representative σ a
    apply (mem_coset_altered_iff σ c _).mpr
    refine ⟨(u : k), u.ne_zero, ?_⟩
    apply congrArg Option.some
    have hv := congrArg (fun z : Fˣ => (z : F)) hu
    simpa [embeddedUnits, ha, mul_comm] using hv

theorem existsUnique_coset_altered (σ : k →+* F) (a : F) (ha : a ≠ 0) :
    ∃! c : CosetIndex σ, some a ∈ alteredDirections σ (cosetPlacement σ c) := by
  refine ⟨unitCoset σ (Units.mk0 a ha), ?_, ?_⟩
  · exact (some_unit_mem_coset_altered_iff σ _ (Units.mk0 a ha)).mpr rfl
  · intro c hc
    exact ((some_unit_mem_coset_altered_iff σ c (Units.mk0 a ha)).mp hc).symm

theorem coset_altered_index_eq (σ : k →+* F) {c e : CosetIndex σ}
    {d : Direction F}
    (hc : d ∈ alteredDirections σ (cosetPlacement σ c))
    (he : d ∈ alteredDirections σ (cosetPlacement σ e)) : c = e := by
  obtain ⟨t, ht, rfl⟩ := (mem_coset_altered_iff σ c d).mp hc
  let a : Fˣ := cosetRepresentative σ c * embeddedUnits σ (Units.mk0 t ht)
  have hc' : unitCoset σ a = c := by
    simp only [a, unitCoset_mul_embedded, unitCoset_representative]
  have he' : unitCoset σ a = e := by
    apply (some_unit_mem_coset_altered_iff σ e a).mp
    simpa [a, embeddedUnits] using he
  exact hc'.symm.trans he'

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [DecidableEq k] [DecidableEq F]

namespace PlaneLinearMap

theorem directionMap_bijective [Fintype F] (M : PlaneLinearMap F) :
    Function.Bijective M.directionMap :=
  M.directionMap_injective.bijective_of_finite

end PlaneLinearMap

theorem extra_placedDirection (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction k) :
    placedDirection σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) d =
      mapDirection σ ((PlaneLinearMap.extra u v huv).directionMap d) := by
  cases d with
  | none =>
      simp [placedDirection, mapDirection]
  | some t =>
      have hzero : 1 + σ t = 0 ↔ 1 + t = 0 := by
        constructor
        · intro h
          apply σ.injective
          simpa only [map_add, map_one, map_zero] using h
        · intro h
          simpa only [map_add, map_one, map_zero] using congrArg σ h
      by_cases ht : 1 + t = 0
      · have hF := hzero.mpr ht
        simp [placedDirection, mapDirection, PlaneLinearMap.directionMap,
          PlaneLinearMap.extra, ht, hF]
      · have hF : 1 + σ t ≠ 0 := fun h => ht (hzero.mp h)
        simp [placedDirection, mapDirection, PlaneLinearMap.directionMap,
          PlaneLinearMap.extra, ht, hF, map_div₀, map_add, map_mul]

variable [instFintypek : Fintype k]

theorem extra_allDirections_image (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    (Finset.univ.image
      (placedDirection σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)))) =
      Finset.univ.image (mapDirection σ) := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr
      ⟨(PlaneLinearMap.extra u v huv).directionMap e, Finset.mem_univ _,
        (extra_placedDirection σ u v huv e).symm⟩
  · intro hd
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨a, ha⟩ := (PlaneLinearMap.extra u v huv).directionMap_bijective.surjective e
    refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
    rw [extra_placedDirection σ u v huv a, ha]

theorem extra_axisDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    axisDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) =
      {some (σ u), some (σ v)} := let _ := instFintypek; by
  simp [axisDirections, placedDirection, mapDirection, Finset.pair_comm]

theorem alteredDirections_eq_allDirections_sdiff_axisDirections
    (σ : k →+* F) (M : PlaneLinearMap F) :
    alteredDirections σ M =
      (Finset.univ.image (placedDirection σ M)) \ axisDirections σ M := by
  ext d
  constructor
  · intro hd
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · obtain ⟨t, _, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
      exact Finset.mem_image.mpr ⟨some t, Finset.mem_univ _, rfl⟩
    · intro ha
      exact Finset.disjoint_left.mp (disjoint_alteredDirections_axisDirections σ M) hd ha
  · intro hd
    obtain ⟨hf, hn⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hf
    rcases Finset.mem_union.mp (placedDirection_mem_altered_or_axis σ M a) with ha | ha
    · exact ha
    · exact False.elim (hn ha)

theorem extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    alteredDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) =
      (Finset.univ.image (mapDirection σ)) \ {some (σ u), some (σ v)} := by
  rw [alteredDirections_eq_allDirections_sdiff_axisDirections,
    extra_allDirections_image σ u v huv, extra_axisDirections σ u v huv]

theorem none_mem_extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    none ∈ alteredDirections σ
      (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  rw [extra_alteredDirections σ u v huv]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩
  · simp

theorem zero_mem_extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    some 0 ∈ alteredDirections σ
      (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  have hσu : σ u ≠ 0 := by
    intro h
    apply hu
    apply σ.injective
    simpa only [map_zero] using h
  have hσv : σ v ≠ 0 := by
    intro h
    apply hv
    apply σ.injective
    simpa only [map_zero] using h
  rw [extra_alteredDirections σ u v huv]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨some 0, Finset.mem_univ _, by simp [mapDirection]⟩
  · simp [Ne.symm hσu, Ne.symm hσv]

theorem diagonal_one_axisDirections_subset_extra_alteredDirections
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0) :
    axisDirections σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) ⊆
      alteredDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  intro d hd
  rcases (mem_axisDirections_iff σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) d).mp hd
      with h | h
  · have hd' : d = none := by simpa [placedDirection, mapDirection] using h
    subst d
    simpa [placedDirection, mapDirection] using none_mem_extra_alteredDirections σ u v huv
  · have hd' : d = some 0 := by simpa [placedDirection, mapDirection] using h
    subst d
    simpa [placedDirection, mapDirection] using zero_mem_extra_alteredDirections σ u v huv hu hv

theorem extra_axisDirections_subset_diagonal_one_alteredDirections
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0) :
    axisDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) ⊆
      alteredDirections σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) := by
  intro d hd
  rw [extra_axisDirections σ u v huv] at hd
  rcases Finset.mem_insert.mp hd with hd | hd
  · subst d
    simpa [placedDirection, mapDirection] using
      placedDirection_mem_alteredDirections σ
        (PlaneLinearMap.diagonal (1 : F) one_ne_zero) u hu
  · have hd' : d = some (σ v) := Finset.mem_singleton.mp hd
    subst d
    simpa [placedDirection, mapDirection] using
      placedDirection_mem_alteredDirections σ
        (PlaneLinearMap.diagonal (1 : F) one_ne_zero) v hv

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k]

def embeddedDirections (σ : k →+* F) : Finset (Direction F) :=
  Finset.univ.image (mapDirection σ)

def groupPlacement (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    ConfigurationGroup σ → PlaneLinearMap F
  | none => PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)
  | some c => cosetPlacement σ c

def groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) :=
  alteredDirections σ (groupPlacement σ u v huv i)

def groupAxes (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) :=
  axisDirections σ (groupPlacement σ u v huv i)

def groupConflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Direction F) := by
  classical
  exact match i with
  | none => embeddedDirections σ
  | some c => if c = 1 then embeddedDirections σ else groupAltered σ u v huv (some c)

theorem groupAltered_card (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupAltered σ u v huv i).card = Fintype.card k - 1 :=
  card_alteredDirections σ _

theorem embeddedDirections_card (σ : k →+* F) :
    (embeddedDirections σ).card = Fintype.card k + 1 := by
  rw [embeddedDirections, Finset.card_image_of_injective _ (mapDirection_injective σ),
    Finset.card_univ, Fintype.card_option]

theorem coset_altered_embedded_index (σ : k →+* F) {c : CosetIndex σ}
    {d : Direction F} (hc : d ∈ alteredDirections σ (cosetPlacement σ c))
    (hd : d ∈ embeddedDirections σ) : c = 1 := by
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hd
  cases e with
  | none =>
      have he' : d = none := he.symm
      subst d
      exact (none_notMem_coset_altered σ c hc).elim
  | some t =>
      have he' : d = some (σ t) := he.symm
      subst d
      have ht : t ≠ 0 := by
        intro ht
        subst t
        exact zero_notMem_coset_altered σ c (by simp [mapDirection] at hc)
      have h1 : some (σ t) ∈ alteredDirections σ (cosetPlacement σ 1) := by
        apply (mem_coset_altered_iff σ 1 _).mpr
        exact ⟨t, ht, by simp⟩
      exact coset_altered_index_eq σ hc h1

theorem identity_altered_subset_embedded (σ : k →+* F) :
    alteredDirections σ (cosetPlacement σ 1) ⊆ embeddedDirections σ := by
  intro d hd
  obtain ⟨t, ht, rfl⟩ := (mem_coset_altered_iff σ 1 d).mp hd
  apply Finset.mem_image.mpr
  exact ⟨some t, Finset.mem_univ _, by simp [mapDirection]⟩

theorem groupAltered_subset_conflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : groupAltered σ u v huv i ⊆ groupConflict σ u v huv i := by
  classical
  cases i with
  | none =>
      intro d hd
      change d ∈ embeddedDirections σ
      change d ∈ alteredDirections σ
        (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) at hd
      rw [extra_alteredDirections σ u v huv] at hd
      exact (Finset.mem_sdiff.mp hd).1
  | some c =>
      by_cases hc : c = 1
      · subst c
        simpa [groupConflict, groupAltered, groupPlacement] using
          identity_altered_subset_embedded σ
      · simp only [groupConflict, ite_eq_right hc]
        exact Finset.Subset.refl _

theorem exists_groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) (d : Direction F) :
    ∃ i : ConfigurationGroup σ, d ∈ groupAltered σ u v huv i := by
  cases d with
  | none => exact ⟨none, none_mem_extra_alteredDirections σ u v huv⟩
  | some a =>
      by_cases ha : a = 0
      · subst a
        exact ⟨none, zero_mem_extra_alteredDirections σ u v huv hu hv⟩
      · obtain ⟨c, hc, _⟩ := existsUnique_coset_altered σ a ha
        exact ⟨some c, hc⟩

theorem shared_groupConflict (σ : k →+* F) (u v : k) (huv : u ≠ v)
    {i j : ConfigurationGroup σ} {d : Direction F} (hij : i ≠ j)
    (hi : d ∈ groupConflict σ u v huv i)
    (hj : d ∈ groupConflict σ u v huv j) :
    (i = none ∧ j = some 1) ∨ (i = some 1 ∧ j = none) := by
  classical
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some c =>
          have hc : c = 1 := by
            by_contra hc
            have hj' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hj
            exact hc (coset_altered_embedded_index σ hj' hi)
          exact Or.inl ⟨rfl, congrArg some hc⟩
  | some c =>
      cases j with
      | none =>
          have hc : c = 1 := by
            by_contra hc
            have hi' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hi
            exact hc (coset_altered_embedded_index σ hi' hj)
          exact Or.inr ⟨congrArg some hc, rfl⟩
      | some e =>
          have hce : c ≠ e := fun h => hij (congrArg some h)
          by_cases hc : c = 1
          · subst c
            have he : e ≠ 1 := Ne.symm hce
            have hj' : d ∈ alteredDirections σ (cosetPlacement σ e) := by
              simpa [groupConflict, he, groupAltered, groupPlacement] using hj
            have hi' : d ∈ embeddedDirections σ := by simpa [groupConflict] using hi
            exact (he (coset_altered_embedded_index σ hj' hi')).elim
          · have hi' : d ∈ alteredDirections σ (cosetPlacement σ c) := by
              simpa [groupConflict, hc, groupAltered, groupPlacement] using hi
            by_cases he : e = 1
            · subst e
              have hj' : d ∈ embeddedDirections σ := by simpa [groupConflict] using hj
              exact (hc (coset_altered_embedded_index σ hi' hj')).elim
            · have hj' : d ∈ alteredDirections σ (cosetPlacement σ e) := by
                simpa [groupConflict, he, groupAltered, groupPlacement] using hj
              exact (hce (coset_altered_index_eq σ hi' hj')).elim

theorem shared_groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    {i j : ConfigurationGroup σ} {d : Direction F} (hij : i ≠ j)
    (hi : d ∈ groupAltered σ u v huv i)
    (hj : d ∈ groupAltered σ u v huv j) :
    (i = none ∧ j = some 1) ∨ (i = some 1 ∧ j = none) :=
  shared_groupConflict σ u v huv hij
    (groupAltered_subset_conflict σ u v huv i hi)
    (groupAltered_subset_conflict σ u v huv j hj)

section FiniteAmbient

variable [Fintype F]

theorem groupConflict_multiplicity_le_two (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)).card ≤ 2 := by
  classical
  let I := Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)
  by_cases hsingle : ∀ i ∈ I, ∀ j ∈ I, i = j
  · have hcard : I.card ≤ 1 := Finset.card_le_one.mpr hsingle
    exact hcard.trans (by decide)
  · push Not at hsingle
    obtain ⟨i, hi, j, hj, hij⟩ := hsingle
    have hsub : I ⊆ ({none, some 1} : Finset (ConfigurationGroup σ)) := by
      intro a ha
      by_cases hai : a = i
      · subst a
        rcases shared_groupConflict σ u v huv hij (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2 with h | h
        · simp [h.1]
        · simp [h.1]
      · rcases shared_groupConflict σ u v huv hai (Finset.mem_filter.mp ha).2
          (Finset.mem_filter.mp hi).2 with h | h
        · simp [h.1]
        · simp [h.1]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem groupAltered_multiplicity_le_two (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ groupAltered σ u v huv i)).card ≤ 2 := by
  apply (Finset.card_le_card ?_).trans (groupConflict_multiplicity_le_two σ u v huv d)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    groupAltered_subset_conflict σ u v huv i (Finset.mem_filter.mp hi).2⟩

end FiniteAmbient

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [Fintype k]

theorem exists_distinct_nonzero (hcard : 2 < Fintype.card k) :
    ∃ u v : k, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  classical
  have hex : ∃ v : k, v ≠ 0 ∧ v ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ] at hc
    omega
  obtain ⟨v, hv0, hv1⟩ := hex
  exact ⟨1, v, one_ne_zero, hv0, hv1.symm⟩

theorem groupAxes_some_one_subset_none (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    groupAxes σ u v huv (some 1) ⊆ groupAltered σ u v huv none := by
  simpa [groupAxes, groupAltered, groupPlacement, cosetPlacement] using
    diagonal_one_axisDirections_subset_extra_alteredDirections σ u v huv hu hv

theorem groupAxes_none_subset_some_one (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    groupAxes σ u v huv none ⊆ groupAltered σ u v huv (some 1) := by
  simpa [groupAxes, groupAltered, groupPlacement, cosetPlacement] using
    extra_axisDirections_subset_diagonal_one_alteredDirections σ u v huv hu hv

theorem shared_groupAltered_axes_subset (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) {i j : ConfigurationGroup σ} {d : Direction F}
    (hij : i ≠ j) (hi : d ∈ groupAltered σ u v huv i)
    (hj : d ∈ groupAltered σ u v huv j) :
    groupAxes σ u v huv i ⊆ groupAltered σ u v huv j := by
  rcases shared_groupAltered σ u v huv hij hi hj with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact groupAxes_none_subset_some_one σ u v huv hu hv
  · rcases h with ⟨rfl, rfl⟩
    exact groupAxes_some_one_subset_none σ u v huv hu hv

theorem groupConflict_card_le (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupConflict σ u v huv i).card ≤ Fintype.card k + 1 := by
  classical
  cases i with
  | none => exact le_of_eq (embeddedDirections_card σ)
  | some c =>
      by_cases hc : c = 1
      · simpa [groupConflict, hc] using le_of_eq (embeddedDirections_card σ)
      · simp only [groupConflict, ite_eq_right hc, groupAltered_card]
        omega

def groupPoints (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) : Finset (Point F) :=
  Finset.univ.image (fun w : Point k => (groupPlacement σ u v huv i).apply (mapPoint σ w))

theorem groupPoints_card (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (i : ConfigurationGroup σ) :
    (groupPoints σ u v huv i).card = Fintype.card k ^ 2 := by
  have hinj : Function.Injective
      (fun w : Point k => (groupPlacement σ u v huv i).apply (mapPoint σ w)) :=
    (groupPlacement σ u v huv i).apply_injective.comp (mapPoint_injective σ)
  rw [groupPoints, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  exact card_point

section FiniteAmbient

variable [Fintype F]

theorem card_groups_mul_sub_one_le (σ : k →+* F) :
    Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1) ≤
      2 * Fintype.card F := let _ := instDecidableEqk; let _ := instDecidableEqF; by
  have hcard : Fintype.card k ≤ Fintype.card F :=
    Fintype.card_le_of_injective σ σ.injective
  rw [card_configurationGroup, Nat.add_mul, card_cosetIndex_mul, one_mul]
  omega

end FiniteAmbient

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientTrialOutcome (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : Point F) :
    LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K) :=
  ambientLineOutcome (deletedLines σ M b a) (by
    rw [card_deletedLines σ M b a ha]
    exact ambientDeletionConstant_lines_le _ _)

def ambientTrialLaw (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) :
    FiniteLaw (LineCover.Outcome (ambientShapes F)
      (ambientDeletionConstant (Fintype.card k) K)) :=
  (FiniteLaw.uniform (Point F)).map (ambientTrialOutcome σ M a ha K)

def ambientPointRate (σ : k →+* F) (M : PlaneLinearMap F) (a : GadgetOutcome k) : ℝ :=
  ((ambientLineUnion (deletedLines σ M 0 a)).card : ℝ) / (Fintype.card F : ℝ) ^ 2

theorem ambientTrialLaw_point_probability (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (x : Point F) :
    (ambientTrialLaw σ M a ha K).prob (fun A => x ∈ LineCover.deleted ∅ A) =
      ambientPointRate σ M a := by
  rw [ambientTrialLaw, FiniteLaw.prob_map]
  simp only [ambientTrialOutcome, deleted_empty_ambientLineOutcome]
  exact uniform_prob_mem_deletedLines_union σ M a x

theorem ambientPointRate_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) :
    ambientPointRate σ M a ≤ ((Fintype.card k - 1 : ℕ) : ℝ) ^ 2 / Fintype.card F := by
  have h := uniform_prob_mem_deletedLines_union_le σ M a (0 : Point F)
  rw [uniform_prob_mem_deletedLines_union, card_deletedLines σ M 0 a ha,
    Nat.cast_pow] at h
  exact h

theorem ambientTrialLaw_line_probability_le (σ : k →+* F) (M : PlaneLinearMap F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (l : AffineLine F) :
    (ambientTrialLaw σ M a ha K).prob (fun A => ∃ S ∈ A.val, S.val = linePoints l) ≤
      if l.1 ∈ alteredDirections σ M then
        ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F else 0 := by
  rw [ambientTrialLaw, FiniteLaw.prob_map]
  simp only [ambientTrialOutcome, ambientLineOutcome_lists_line]
  have h := uniform_prob_mem_deletedLines_le σ M a l
  by_cases hd : l.1 ∈ alteredDirections σ M
  · rw [ite_eq_left hd]
    rw [card_deletedLines_of_mem_alteredDirections σ M 0 a ha l.1 hd] at h
    exact h
  · rw [ite_eq_right hd]
    have hempty : ((deletedLines σ M 0 a).filter (fun e => e.1 = l.1)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he, hdir⟩ := Finset.mem_filter.mp he
      have hedir := ((mem_deletedLines σ M 0 a e).mp he).1
      exact hd (hdir ▸ hedir)
    simpa only [hempty, Finset.card_empty, Nat.cast_zero, zero_div] using h

abbrev AmbientPosition (σ : k →+* F) (K : ℕ) := ConfigurationGroup σ × Fin K

def ambientTrialCount (σ : k →+* F) (K : ℕ) : ℕ := Fintype.card (AmbientPosition σ K)

def ambientPosition (σ : k →+* F) (K : ℕ) (t : Fin (ambientTrialCount σ K)) :
    AmbientPosition σ K := (Fintype.equivFin (AmbientPosition σ K)).symm t

def ambientTrials (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (t : Fin (ambientTrialCount σ K)) :
    FiniteLaw (LineCover.Outcome (ambientShapes F)
      (ambientDeletionConstant (Fintype.card k) K)) :=
  ambientTrialLaw σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K

theorem ambientTrialCount_mul_sub_one_le (σ : k →+* F) (K : ℕ) :
    ambientTrialCount σ K * (Fintype.card k - 1) ≤ 2 * K * Fintype.card F := by
  unfold ambientTrialCount AmbientPosition
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    Fintype.card (ConfigurationGroup σ) * K * (Fintype.card k - 1) =
        K * (Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1)) := by ring
    _ ≤ K * (2 * Fintype.card F) :=
      Nat.mul_le_mul_left K (card_groups_mul_sub_one_le σ)
    _ = 2 * K * Fintype.card F := by ring

theorem ambientTrialCount_le (σ : k →+* F) (K : ℕ) (hs : 2 ≤ Fintype.card k) :
    ambientTrialCount σ K ≤ ambientDeletionConstant (Fintype.card k) K * Fintype.card F := by
  have hs' : 1 ≤ Fintype.card k - 1 := by omega
  calc
    ambientTrialCount σ K = ambientTrialCount σ K * 1 := by rw [Nat.mul_one]
    _ ≤ ambientTrialCount σ K * (Fintype.card k - 1) := Nat.mul_le_mul_left _ hs'
    _ ≤ 2 * K * Fintype.card F := ambientTrialCount_mul_sub_one_le σ K
    _ ≤ ambientDeletionConstant (Fintype.card k) K * Fintype.card F :=
      Nat.mul_le_mul_right _ (ambientDeletionConstant_trials_le _ _)

theorem ambientTrials_line_probability_sum_le (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (l : AffineLine F) :
    (∑ t, (ambientTrials σ u v huv a ha K t).prob
      (fun A => ∃ S ∈ A.val, S.val = linePoints l)) ≤
      (2 : ℝ) * K * ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F := by
  let rate : ℝ := ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F
  have hrate : 0 ≤ rate := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum : (∑ i : ConfigurationGroup σ,
      if l.1 ∈ groupAltered σ u v huv i then rate else 0) ≤ 2 * rate := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hmult : ((Finset.univ.filter
        (fun i => l.1 ∈ groupAltered σ u v huv i)).card : ℝ) ≤ 2 := by
      exact_mod_cast groupAltered_multiplicity_le_two σ u v huv l.1
    exact mul_le_mul_of_nonneg_right hmult hrate
  calc
    _ = ∑ p : AmbientPosition σ K,
        (ambientTrialLaw σ (groupPlacement σ u v huv p.1) a ha K).prob
          (fun A => ∃ S ∈ A.val, S.val = linePoints l) :=
      Equiv.sum_comp (Fintype.equivFin (AmbientPosition σ K)).symm _
    _ ≤ ∑ i : ConfigurationGroup σ, ∑ _j : Fin K,
        if l.1 ∈ groupAltered σ u v huv i then rate else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact ambientTrialLaw_line_probability_le σ (groupPlacement σ u v huv i) a ha K l
    _ = (K : ℝ) * ∑ i : ConfigurationGroup σ,
        if l.1 ∈ groupAltered σ u v huv i then rate else 0 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (2 * rate) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (2 : ℝ) * K * ((Fintype.card k - 1 : ℕ) : ℝ) / Fintype.card F := by
      dsimp only [rate]
      ring

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Construction

noncomputable def ambientDeletionDelta (s K : ℕ) : ℝ :=
  Real.exp (-4 * (K : ℝ) * ((s - 1 : ℕ) : ℝ))

theorem ambientDeletionDelta_pos (s K : ℕ) : 0 < ambientDeletionDelta s K :=
  Real.exp_pos _

theorem neg_two_mul_le_log_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    -2 * t ≤ Real.log (1 - t) := by
  have hb : 0 < 1 - t := by linarith
  have hratio : t / (1 - t) ≤ 2 * t := by
    apply (div_le_iff₀ hb).2
    have hmul := mul_nonneg ht0 (show 0 ≤ 1 - 2 * t by linarith)
    nlinarith only [hmul]
  have hid : 1 - (1 - t)⁻¹ = -(t / (1 - t)) := by
    field_simp [hb.ne']
    ring
  calc
    -2 * t ≤ -(t / (1 - t)) := by linarith only [hratio]
    _ = 1 - (1 - t)⁻¹ := hid.symm
    _ ≤ Real.log (1 - t) := Real.one_sub_inv_le_log_of_pos hb

theorem exp_neg_two_mul_le_one_sub_pow (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.exp (-2 * (N : ℝ) * t) ≤ (1 - t) ^ N := by
  have hb : 0 < 1 - t := by linarith
  apply (Real.le_log_iff_exp_le (pow_pos hb N)).mp
  rw [Real.log_pow]
  have hlog := mul_le_mul_of_nonneg_left (neg_two_mul_le_log_one_sub ht0 ht)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))
  nlinarith only [hlog]

theorem ambientDeletionDelta_le_pow (s K q N : ℕ) (hs : 2 ≤ s) (hq : 0 < q)
    (hsmall : 2 * (s - 1) ^ 2 ≤ q) (hcount : N * (s - 1) ≤ 2 * K * q) :
    ambientDeletionDelta s K ≤ (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) ^ N := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hm : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hs)
  have hsmall' : (2 : ℝ) * ((s - 1 : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast hsmall
  have hcount' : (N : ℝ) * ((s - 1 : ℕ) : ℝ) ≤ 2 * (K : ℝ) * (q : ℝ) := by
    exact_mod_cast hcount
  let t : ℝ := ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (sq_nonneg _) hq'.le
  have ht : t ≤ 1 / 2 := by
    apply (div_le_iff₀ hq').2
    nlinarith only [hsmall']
  have htotal : (N : ℝ) * t ≤ 2 * (K : ℝ) * ((s - 1 : ℕ) : ℝ) := by
    dsimp only [t]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hq').2
    have hmul := mul_le_mul_of_nonneg_right hcount' hm.le
    nlinarith only [hmul]
  have hexponent : -4 * (K : ℝ) * ((s - 1 : ℕ) : ℝ) ≤ -2 * (N : ℝ) * t := by
    nlinarith only [htotal]
  unfold ambientDeletionDelta
  exact (Real.exp_le_exp.mpr hexponent).trans
    (exp_neg_two_mul_le_one_sub_pow N ht0 ht)

theorem ambientDeletionDelta_le_finset_prod {ι : Type*} (I : Finset ι)
    (s K q : ℕ) (hs : 2 ≤ s) (hq : 0 < q) (hsmall : 2 * (s - 1) ^ 2 ≤ q)
    (hcount : I.card * (s - 1) ≤ 2 * K * q) (p : ι → ℝ)
    (hp : ∀ i ∈ I, p i ≤ ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) :
    ambientDeletionDelta s K ≤ ∏ i ∈ I, (1 - p i) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsmall' : (2 : ℝ) * ((s - 1 : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast hsmall
  have hhalf : ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hq').2
    nlinarith only [hsmall']
  have hbase : 0 ≤ 1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ) := by linarith
  apply (ambientDeletionDelta_le_pow s K q I.card hs hq hsmall hcount).trans
  calc
    (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) ^ I.card =
        ∏ _i ∈ I, (1 - ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) := by
      rw [Finset.prod_const]
    _ ≤ ∏ i ∈ I, (1 - p i) :=
      Finset.prod_le_prod (fun _ _ => hbase)
        (fun i hi => sub_le_sub_left (hp i hi) 1)

theorem ambientDeletionDelta_le_prod {ι : Type*} [Fintype ι]
    (s K q : ℕ) (hs : 2 ≤ s) (hq : 0 < q) (hsmall : 2 * (s - 1) ^ 2 ≤ q)
    (hcount : Fintype.card ι * (s - 1) ≤ 2 * K * q) (p : ι → ℝ)
    (hp : ∀ i, p i ≤ ((s - 1 : ℕ) : ℝ) ^ 2 / (q : ℝ)) :
    ambientDeletionDelta s K ≤ ∏ i, (1 - p i) := by
  classical
  apply ambientDeletionDelta_le_finset_prod Finset.univ s K q hs hq hsmall ?_ p ?_
  · simpa only [Finset.card_univ] using hcount
  · intro i _
    exact hp i

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientSurvival (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) : ℝ :=
  ∏ t : Fin (ambientTrialCount σ K),
    (1 - ambientPointRate σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a)

theorem ambientTrials_uniformSurvival (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (x : Point F) :
    (FiniteLaw.pi (ambientTrials σ u v huv a ha K)).prob
      (fun ω => x ∈ LineCover.survivors ∅ ω) = ambientSurvival σ u v huv a K := by
  simp only [LineCover.mem_survivors]
  rw [FiniteLaw.prob_pi (ambientTrials σ u v huv a ha K)
    (fun _ A => x ∉ LineCover.deleted ∅ A)]
  simp_rw [FiniteLaw.prob_compl]
  simp only [ambientTrials, ambientTrialLaw_point_probability, ambientSurvival]

theorem ambientSurvival_lower (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (hs : 2 ≤ Fintype.card k)
    (hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F) :
    ambientDeletionDelta (Fintype.card k) K ≤ ambientSurvival σ u v huv a K := by
  apply ambientDeletionDelta_le_prod (Fintype.card k) K (Fintype.card F) hs
    Fintype.card_pos hsmall ?_ _ ?_
  · simpa only [Fintype.card_fin] using ambientTrialCount_mul_sub_one_le σ K
  · intro t
    exact ambientPointRate_le σ (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha

def ambientDeletionProcess (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (hs : 2 ≤ Fintype.card k)
    (hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F) :
    LineCover.DeletionProcess F (ambientDeletionConstant (Fintype.card k) K)
      (ambientDeletionDelta (Fintype.card k) K) where
  shapes := ambientShapes F
  shapeCount := ambientShapes_count_le (ambientDeletionConstant_two_le _ _)
  shapeSize := ambientShapes_size_le (le_trans (by decide) (ambientDeletionConstant_two_le _ _))
  sparse := ambientShapes_sparse (le_trans (by decide) (ambientDeletionConstant_two_le _ _))
  trialsCount := ambientTrialCount σ K
  trials := ambientTrials σ u v huv a ha K
  trialsCount_le := ambientTrialCount_le σ K hs
  pointCap := by
    intro t x
    rw [ambientTrials, ambientTrialLaw_point_probability]
    apply (ambientPointRate_le σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast ambientDeletionConstant_lines_le (Fintype.card k) K
  survival := ambientSurvival σ u v huv a K
  survivalLower := ambientSurvival_lower σ u v huv a ha K hs hsmall
  uniformSurvival := ambientTrials_uniformSurvival σ u v huv a ha K
  lineCap := by
    intro l
    apply (ambientTrials_line_probability_sum_le σ u v huv a ha K l).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast ambientDeletionConstant_lineRate_le (Fintype.card k) K

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

def ShiftHits (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (b : Point F) : Prop :=
  ∃ w ∈ W, ∃ d ∈ S, Incidence (b + w) ell ∧
    projection d (b + w) = projection d p

def badShifts (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) : Finset (Point F) := by
  classical
  exact Finset.univ.filter (ShiftHits W S p ell)

@[simp] theorem mem_badShifts (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (b : Point F) :
    b ∈ badShifts W S p ell ↔ ShiftHits W S p ell b := let _ := instDecidableEqF; by
  classical
  simp only [badShifts, Finset.mem_filter, Finset.mem_univ, true_and]

theorem badShifts_eq_biUnion (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) :
    badShifts W S p ell = W.biUnion (fun w => S.biUnion (fun d =>
      (linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w))) := by
  ext b
  constructor
  · intro hb
    obtain ⟨w, hw, d, hd, hbell, hbd⟩ := (mem_badShifts W S p ell b).mp hb
    apply Finset.mem_biUnion.mpr
    refine ⟨w, hw, Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨b + w, Finset.mem_inter.mpr ⟨?_, ?_⟩, by simp⟩
    · exact (mem_linePoints _ _).mpr hbell
    · exact (mem_linePoints _ _).mpr hbd
  · intro hb
    obtain ⟨w, hw, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨d, hd, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
    apply (mem_badShifts W S p ell b).mpr
    have hby : b + w = y := by rw [← hyb]; simp
    refine ⟨w, hw, d, hd, ?_, ?_⟩
    · rw [hby]
      exact (mem_linePoints _ _).mp (Finset.mem_inter.mp hy).1
    · rw [hby]
      exact (mem_linePoints _ _).mp (Finset.mem_inter.mp hy).2

theorem badShifts_card_le (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (badShifts W S p ell).card ≤ W.card * S.card := by
  have hpoint (d : Direction F) :
      (linePoints ell ∩ linePoints (lineThrough d p)).card ≤ 1 := by
    apply card_linePoints_inter_le_one
    intro heq
    exact hp (heq.symm ▸ incidence_lineThrough d p)
  rw [badShifts_eq_biUnion]
  calc
    _ ≤ ∑ w ∈ W, (S.biUnion (fun d =>
        (linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ W, S.card := by
      apply Finset.sum_le_sum
      intro w hw
      calc
        _ ≤ ∑ d ∈ S,
            ((linePoints ell ∩ linePoints (lineThrough d p)).image (fun y => y - w)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _d ∈ S, 1 := Finset.sum_le_sum fun d _ =>
          Finset.card_image_le.trans (hpoint d)
        _ = S.card := by simp
    _ = W.card * S.card := by simp

theorem uniform_prob_shiftHits_le (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Point F)).prob (ShiftHits W S p ell) ≤
      (W.card : ℝ) * S.card / (Fintype.card F : ℝ) ^ 2 := by
  classical
  rw [FiniteLaw.uniform_prob]
  change ((badShifts W S p ell).card : ℝ) / Fintype.card (Point F) ≤ _
  rw [card_point, Nat.cast_pow]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast badShifts_card_le W S p ell hp
  · positivity

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def poolThinLaw (G : Type*) [Fintype G] [DecidableEq G] (K : ℕ) :
    FiniteLaw (G → Fin K → Point F) :=
  FiniteLaw.pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))

def poolGroupBad {K : ℕ} (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (a : Fin K → Point F) : Prop :=
  ∃ j, ShiftHits W S p ell (a j)

variable {G : Type*} [Fintype G] [DecidableEq G] {K : ℕ}

def poolBadGroups (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (ω : G → Fin K → Point F) : Finset G :=
  Finset.univ.filter (fun i => poolGroupBad (W i) (S i) p ell (ω i))

def PoolThin (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (ω : G → Fin K → Point F) : Prop :=
  ∀ p ell, ¬ Incidence p ell → (poolBadGroups W S p ell ω).card ≤ 5

theorem uniform_prob_poolGroupBad_le
    (W : Finset (Point F)) (S : Finset (Direction F))
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Fin K → Point F)).prob (poolGroupBad W S p ell) ≤
      (K : ℝ) * W.card * S.card / (Fintype.card F : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ j : Fin K, (FiniteLaw.uniform (Fin K → Point F)).prob
        (fun a => ShiftHits W S p ell (a j)) :=
      FiniteLaw.prob_exists_le _ _
    _ = ∑ _j : Fin K, (FiniteLaw.uniform (Point F)).prob
        (ShiftHits W S p ell) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← FiniteLaw.pi_uniform]
      exact FiniteLaw.prob_pi_coordinate
        (fun _ : Fin K => FiniteLaw.uniform (Point F)) j (ShiftHits W S p ell)
    _ ≤ ∑ _j : Fin K,
        (W.card : ℝ) * S.card / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun _ _ => uniform_prob_shiftHits_le W S p ell hp)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem uniform_prob_poolGroupBad_le_of_card
    (W : Finset (Point F)) (S : Finset (Direction F))
    (w s : ℕ) (hW : W.card ≤ w) (hS : S.card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (FiniteLaw.uniform (Fin K → Point F)).prob (poolGroupBad W S p ell) ≤
      (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2 := by
  refine (uniform_prob_poolGroupBad_le W S p ell hp).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left K hW) hS

theorem poolThinLaw_prob_all_bad_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) (T : Finset G) :
    (poolThinLaw (F := F) G K).prob
        (fun ω => ∀ i ∈ T, poolGroupBad (W i) (S i) p ell (ω i)) ≤
      ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ T.card := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  change (FiniteLaw.pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))).prob
    (fun ω => ∀ i, i ∈ T → poolGroupBad (W i) (S i) p ell (ω i)) ≤ b ^ T.card
  rw [FiniteLaw.prob_pi (fun _ : G => FiniteLaw.uniform (Fin K → Point F))
    (fun i a => i ∈ T → poolGroupBad (W i) (S i) p ell a)]
  calc
    _ ≤ ∏ i : G, if i ∈ T then b else 1 := by
      apply Finset.prod_le_prod
      · intro i _
        exact FiniteLaw.prob_nonneg _ _
      · intro i _
        by_cases hi : i ∈ T
        · simpa [hi] using
            uniform_prob_poolGroupBad_le_of_card (K := K)
              (W i) (S i) w s (hW i) (hS i) p ell hp
        · simp [hi]
    _ = b ^ T.card := by
      rw [Finset.prod_ite_mem_eq]
      exact Finset.prod_const b

theorem poolThinLaw_prob_six_bad_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s)
    (p : Point F) (ell : AffineLine F) (hp : ¬ Incidence p ell) :
    (poolThinLaw (F := F) G K).prob
        (fun ω => 6 ≤ (poolBadGroups W S p ell ω).card) ≤
      (Fintype.card G : ℝ) ^ 6 *
        ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ 6 := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let C : Finset (Finset G) := (Finset.univ : Finset G).powersetCard 6
  change (poolThinLaw (F := F) G K).prob
    (fun ω => 6 ≤ (poolBadGroups W S p ell ω).card) ≤
      (Fintype.card G : ℝ) ^ 6 * b ^ 6
  calc
    _ ≤ (poolThinLaw (F := F) G K).prob
        (fun ω => ∃ T : ↥C, ∀ i ∈ T.val, poolGroupBad (W i) (S i) p ell (ω i)) := by
      apply FiniteLaw.prob_mono
      intro ω hω
      obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
      refine ⟨⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hT hi)).2
    _ ≤ ∑ T : ↥C, (poolThinLaw (F := F) G K).prob
        (fun ω => ∀ i ∈ T.val, poolGroupBad (W i) (S i) p ell (ω i)) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _T : ↥C, b ^ 6 := by
      apply Finset.sum_le_sum
      intro T _
      have hT := poolThinLaw_prob_all_bad_le (K := K) W S w s hW hS p ell hp T.val
      have hcard : T.val.card = 6 := (Finset.mem_powersetCard.mp T.property).2
      simpa only [hcard] using hT
    _ = ((Fintype.card G).choose 6 : ℝ) * b ^ 6 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        C, Finset.card_powersetCard, nsmul_eq_mul]
    _ ≤ (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb _)
      exact_mod_cast Nat.choose_le_pow (Fintype.card G) 6

theorem prob_not_poolThin_le
    (W : G → Finset (Point F)) (S : G → Finset (Direction F))
    (w s : ℕ) (hW : ∀ i, (W i).card ≤ w) (hS : ∀ i, (S i).card ≤ s) :
    (poolThinLaw (F := F) G K).prob (fun ω => ¬ PoolThin W S ω) ≤
      (Fintype.card F : ℝ) ^ 3 * ((Fintype.card F : ℝ) + 1) *
        (Fintype.card G : ℝ) ^ 6 *
          ((K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2) ^ 6 := by
  let b : ℝ := (K : ℝ) * w * s / (Fintype.card F : ℝ) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by positivity
  change (poolThinLaw (F := F) G K).prob (fun ω => ¬ PoolThin W S ω) ≤
    (Fintype.card F : ℝ) ^ 3 * ((Fintype.card F : ℝ) + 1) *
      (Fintype.card G : ℝ) ^ 6 * b ^ 6
  calc
    _ ≤ (poolThinLaw (F := F) G K).prob
        (fun ω => ∃ z : Point F × AffineLine F,
          ¬ Incidence z.1 z.2 ∧ 6 ≤ (poolBadGroups W S z.1 z.2 ω).card) := by
      apply FiniteLaw.prob_mono
      intro ω hω
      by_contra hn
      apply hω
      intro p ell hp
      by_contra hcard
      apply hn
      refine ⟨(p, ell), hp, ?_⟩
      change 6 ≤ (poolBadGroups W S p ell ω).card
      omega
    _ ≤ ∑ z : Point F × AffineLine F, (poolThinLaw (F := F) G K).prob
        (fun ω => ¬ Incidence z.1 z.2 ∧
          6 ≤ (poolBadGroups W S z.1 z.2 ω).card) :=
      FiniteLaw.prob_exists_le _ _
    _ ≤ ∑ _z : Point F × AffineLine F, (Fintype.card G : ℝ) ^ 6 * b ^ 6 := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hp : Incidence z.1 z.2
      · simpa [hp] using hB
      · simpa [hp] using
          poolThinLaw_prob_six_bad_le (K := K) W S w s hW hS z.1 z.2 hp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        card_direction, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Selection

variable (F : Type*) [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] (n K : ℕ)

theorem poolLaw_eq_uniform : poolLaw F n K = FiniteLaw.uniform (Pool F n K) := let _ := instDecidableEqF;
  FiniteLaw.pi_uniform

variable {F n K}

abbrev ExposedAssignment (T : Finset (Position n K)) :=
  {e : Position n K // e ∈ T} → Point F

abbrev FreshAssignment (T : Finset (Position n K)) :=
  {e : Position n K // e ∉ T} → Point F

def joinAssignments (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T) :
    Pool F n K :=
  (Equiv.piEquivPiSubtypeProd (fun e : Position n K => e ∈ T)
    (fun _ => Point F)).symm (x, y)

@[simp] theorem joinAssignments_exposed (T : Finset (Position n K))
    (x : ExposedAssignment (F := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; F) T) (y : FreshAssignment (F := F) T)
    (e : {e : Position n K // e ∈ T}) : joinAssignments T x y e.val = x e := by
  simp [joinAssignments, Equiv.piEquivPiSubtypeProd, e.property]

@[simp] theorem joinAssignments_fresh (T : Finset (Position n K))
    (x : ExposedAssignment (F := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; F) T) (y : FreshAssignment (F := F) T)
    (e : {e : Position n K // e ∉ T}) : joinAssignments T x y e.val = y e := by
  simp [joinAssignments, Equiv.piEquivPiSubtypeProd, e.property]

end RyserCoveringCounterexample.Selection

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [instFintypeK : Fintype k] [Fintype F]
  [instDecidableEqK : DecidableEq k] [DecidableEq F]

abbrev AmbientPool (σ : k →+* F) (K : ℕ) := ConfigurationGroup σ → Fin K → Point F

def ambientPoolTrialEquiv (σ : k →+* F) (K : ℕ) :
    AmbientPool σ K ≃ (Fin (ambientTrialCount σ K) → Point F) where
  toFun b t := b (ambientPosition σ K t).1 (ambientPosition σ K t).2
  invFun b i j := b ((Fintype.equivFin (AmbientPosition σ K)) (i, j))
  left_inv b := by
    funext i j
    simp only [ambientPosition, Equiv.symm_apply_apply]
  right_inv b := by
    funext t
    change b ((Fintype.equivFin (AmbientPosition σ K))
      ((Fintype.equivFin (AmbientPosition σ K)).symm t)) = b t
    exact congrArg b ((Fintype.equivFin (AmbientPosition σ K)).apply_symm_apply t)

def ambientFlatPoolEquiv (σ : k →+* F) (K : ℕ) :
    AmbientPool σ K ≃ Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K where
  toFun b p := b ((Fintype.equivFin (ConfigurationGroup σ)).symm p.1) p.2
  invFun b i j := b ((Fintype.equivFin (ConfigurationGroup σ)) i, j)
  left_inv b := by
    funext i j
    simp only [Equiv.symm_apply_apply]
  right_inv b := by
    funext p
    simp only [Equiv.apply_symm_apply, Prod.mk.eta]

theorem poolThinLaw_map_ambientFlatPoolEquiv (σ : k →+* F) (K : ℕ) :
    (poolThinLaw (F := F) (ConfigurationGroup σ) K).map (ambientFlatPoolEquiv σ K) =
      Selection.poolLaw F (Fintype.card (ConfigurationGroup σ)) K :=
  let _ := instFintypeK; let _ := instDecidableEqK; by
  rw [poolThinLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv,
    Selection.poolLaw_eq_uniform]

def ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K) :
    Fin (ambientTrialCount σ K) →
      LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K) :=
  fun t => ambientTrialOutcome σ
    (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K
    (b (ambientPosition σ K t).1 (ambientPosition σ K t).2)

@[simp] theorem ambientPoolConfig_at (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (i : ConfigurationGroup σ) (j : Fin K) :
    ambientPoolConfig σ u v huv a ha K b
        ((Fintype.equivFin (AmbientPosition σ K)) (i, j)) =
      ambientTrialOutcome σ (groupPlacement σ u v huv i) a ha K (b i j) := by
  simp only [ambientPoolConfig, ambientPosition, Equiv.symm_apply_apply]

theorem poolThinLaw_map_ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) :
    (poolThinLaw (F := F) (ConfigurationGroup σ) K).map
        (ambientPoolConfig σ u v huv a ha K) =
      FiniteLaw.pi (ambientTrials σ u v huv a ha K) := by
  let f : (Fin (ambientTrialCount σ K) → Point F) →
      (Fin (ambientTrialCount σ K) →
        LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K)) :=
    fun b t => ambientTrialOutcome σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K (b t)
  have hconfig : ambientPoolConfig σ u v huv a ha K = f ∘ ambientPoolTrialEquiv σ K := rfl
  rw [hconfig, ← FiniteLaw.map_map]
  have hreindex : (poolThinLaw (F := F) (ConfigurationGroup σ) K).map
      (ambientPoolTrialEquiv σ K) =
      FiniteLaw.pi (fun _ : Fin (ambientTrialCount σ K) => FiniteLaw.uniform (Point F)) := by
    rw [poolThinLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv, FiniteLaw.pi_uniform]
  rw [hreindex]
  exact FiniteLaw.map_pi (fun _ => FiniteLaw.uniform (Point F))
    (fun t => ambientTrialOutcome σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [DecidableEq k] [DecidableEq F]

theorem mem_range_placedPoint_of_incident_of_ne_placedLines
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    {p : Point F} {l m : AffineLine k}
    (hlm : placedLine σ M b l ≠ placedLine σ M b m)
    (hpl : Incidence p (placedLine σ M b l))
    (hpm : Incidence p (placedLine σ M b m)) :
    p ∈ Set.range (placedPoint σ M b) := by
  have hdir : l.1 ≠ m.1 := by
    intro hsame
    have hplaced : (placedLine σ M b l).1 = (placedLine σ M b m).1 := by
      simpa only [placedLine_direction] using congrArg (placedDirection σ M) hsame
    exact hlm (line_eq_of_direction_eq_of_incidence
      (l := placedLine σ M b l) (m := placedLine σ M b m) (p := p)
      hplaced hpl hpm)
  obtain ⟨q, hq, _⟩ := existsUnique_incident_of_ne_direction l m hdir
  have hql : Incidence (placedPoint σ M b q) (placedLine σ M b l) :=
    (incidence_placedLine_iff σ M b q l).2 hq.1
  have hqm : Incidence (placedPoint σ M b q) (placedLine σ M b m) :=
    (incidence_placedLine_iff σ M b q m).2 hq.2
  have hpq : p = placedPoint σ M b q :=
    eq_of_common_incidence_of_ne_lines hlm hpl hpm hql hqm
  exact ⟨q, hpq.symm⟩

theorem eq_placedLine_of_incident_of_notMem_range
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    {p : Point F} {l m : AffineLine k}
    (houtside : p ∉ Set.range (placedPoint σ M b))
    (hpl : Incidence p (placedLine σ M b l))
    (hpm : Incidence p (placedLine σ M b m)) :
    placedLine σ M b l = placedLine σ M b m := by
  by_contra hlm
  exact houtside (mem_range_placedPoint_of_incident_of_ne_placedLines σ M b hlm hpl hpm)

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [instFintypeF : Fintype F] [instDecidableEqk : DecidableEq k] [DecidableEq F]

def placedSubplane (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F) :
    Finset (Point F) := Finset.univ.image (placedPoint σ M b)

@[simp] theorem mem_placedSubplane_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b p : Point F) : p ∈ placedSubplane σ M b ↔ p ∈ Set.range (placedPoint σ M b) := let _ := instFintypeF; let _ := instDecidableEqk; by
  simp only [placedSubplane, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]

theorem exists_placedLine_of_mem_deletedLines (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) {ell : AffineLine F}
    (hell : ell ∈ deletedLines σ M b a) :
    ∃ l : AffineLine k, placedLine σ M b l = ell := by
  have hmem : ell.1 ∈ alteredDirections σ M ∧
      ∃ y ∈ retainedPoints a, Incidence (placedPoint σ M b y) ell := by
    simpa only [deletedLines, Finset.mem_filter, Finset.mem_univ, true_and] using hell
  obtain ⟨t, _, ht⟩ := (mem_alteredDirections_iff σ M ell.1).mp hmem.1
  obtain ⟨y, _, hy⟩ := hmem.2
  refine ⟨(some t, projection (some t) y), ?_⟩
  exact (eq_placedLine_of_direction_of_incidence σ M b y (some t) ell ht.symm hy).symm

theorem eq_deletedLine_of_incident_of_notMem_placedSubplane
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    {p : Point F} {ell m : AffineLine F}
    (houtside : p ∉ placedSubplane σ M b)
    (hell : ell ∈ deletedLines σ M b a) (hm : m ∈ deletedLines σ M b a)
    (hpell : Incidence p ell) (hpm : Incidence p m) : ell = m := by
  have hout : p ∉ Set.range (placedPoint σ M b) := by
    simpa only [mem_placedSubplane_iff] using houtside
  obtain ⟨l, rfl⟩ := exists_placedLine_of_mem_deletedLines σ M b a hell
  obtain ⟨l', rfl⟩ := exists_placedLine_of_mem_deletedLines σ M b a hm
  exact eq_placedLine_of_incident_of_notMem_range σ M b hout hpell hpm

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {G k F : Type*} [Field k] [Field F]
variable [instFintypeG : Fintype G] [Fintype k] [Fintype F]
variable [instDecidableEqG : DecidableEq G] [DecidableEq k] [DecidableEq F]

def DeletionSeparated (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) : Prop :=
  ∀ i j : G, i ≠ j → ∀ p ∈ placedSubplane σ (M i) (b i),
    ∀ y ∈ (retainedPoints a).image (placedPoint σ (M j) (b j)),
      ∀ d ∈ alteredDirections σ (M j), projection d p ≠ projection d y

def allDeletedLines (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) : Finset (AffineLine F) :=
  Finset.univ.biUnion (fun i => deletedLines σ (M i) (b i) a)

def deletedPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) : Finset (AffineLine F) :=
  (allDeletedLines σ M b a).filter (fun ell => Incidence p ell)

def activeDeletionGroups (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) : Finset G :=
  Finset.univ.filter (fun i => ∃ ell ∈ deletedLines σ (M i) (b i) a, Incidence p ell)

@[simp] theorem mem_allDeletedLines (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (ell : AffineLine F) :
    ell ∈ allDeletedLines σ M b a ↔ ∃ i, ell ∈ deletedLines σ (M i) (b i) a := let _ := instDecidableEqG; by
  simp only [allDeletedLines, Finset.mem_biUnion, Finset.mem_univ, true_and]

@[simp] theorem mem_deletedPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) (ell : AffineLine F) :
    ell ∈ deletedPencil σ M b a p ↔
      ell ∈ allDeletedLines σ M b a ∧ Incidence p ell := let _ := instDecidableEqG; by
  simp only [deletedPencil, Finset.mem_filter]

@[simp] theorem mem_activeDeletionGroups (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F) (i : G) :
    i ∈ activeDeletionGroups σ M b a p ↔
      ∃ ell ∈ deletedLines σ (M i) (b i) a, Incidence p ell := let _ := instDecidableEqG; by
  simp only [activeDeletionGroups, Finset.mem_filter, Finset.mem_univ, true_and]

theorem not_incidence_deletedLines_of_mem_other_subplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F) (a : GadgetOutcome k)
    (hsep : DeletionSeparated σ M b a) {i j : G} (hij : i ≠ j)
    {p : Point F} (hp : p ∈ placedSubplane σ (M i) (b i))
    {ell : AffineLine F} (hell : ell ∈ deletedLines σ (M j) (b j) a) :
    ¬Incidence p ell := let _ := instFintypeG; let _ := instDecidableEqG; by
  obtain ⟨hdir, y, hy, hyell⟩ := (mem_deletedLines σ (M j) (b j) a ell).mp hell
  have hyplaced : placedPoint σ (M j) (b j) y ∈
      (retainedPoints a).image (placedPoint σ (M j) (b j)) :=
    Finset.mem_image.mpr ⟨y, hy, rfl⟩
  intro hpell
  exact hsep i j hij p hp (placedPoint σ (M j) (b j) y) hyplaced ell.1 hdir
    (hpell.trans hyell.symm)

theorem disjoint_deletedLines_of_separated
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F) (a : GadgetOutcome k)
    (hsep : DeletionSeparated σ M b a) {i j : G} (hij : i ≠ j) :
    Disjoint (deletedLines σ (M i) (b i) a) (deletedLines σ (M j) (b j) a) := by
  apply Finset.disjoint_left.mpr
  intro ell helli hellj
  obtain ⟨y, _, hyell⟩ := ((mem_deletedLines σ (M i) (b i) a ell).mp helli).2
  have hyplane : placedPoint σ (M i) (b i) y ∈ placedSubplane σ (M i) (b i) :=
    (mem_placedSubplane_iff σ (M i) (b i) _).mpr ⟨y, rfl⟩
  exact not_incidence_deletedLines_of_mem_other_subplane
    σ M b a hsep hij hyplane hellj hyell

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]

def groupSelectionData (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    Selection.Data F (Fintype.card (ConfigurationGroup σ)) where
  W i := groupPoints σ u v huv ((Fintype.equivFin (ConfigurationGroup σ)).symm i)
  dirs i := groupConflict σ u v huv ((Fintype.equivFin (ConfigurationGroup σ)).symm i)

@[simp] theorem groupSelectionData_W_equivFin (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (i : ConfigurationGroup σ) :
    (groupSelectionData σ u v huv).W ((Fintype.equivFin (ConfigurationGroup σ)) i) =
      groupPoints σ u v huv i := by
  simp only [groupSelectionData, Equiv.symm_apply_apply]

@[simp] theorem groupSelectionData_dirs_equivFin (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (i : ConfigurationGroup σ) :
    (groupSelectionData σ u v huv).dirs ((Fintype.equivFin (ConfigurationGroup σ)) i) =
      groupConflict σ u v huv i := by
  simp only [groupSelectionData, Equiv.symm_apply_apply]

def groupSelectionConstant (s : ℕ) : ℕ := s ^ 2 + s + 2

theorem card_groups_le_two_mul_card (σ : k →+* F)
    (hs : 2 ≤ Fintype.card k) :
    Fintype.card (ConfigurationGroup σ) ≤ 2 * Fintype.card F := by
  have hfactor : 1 ≤ Fintype.card k - 1 := by omega
  have hle : Fintype.card (ConfigurationGroup σ) ≤
      Fintype.card (ConfigurationGroup σ) * (Fintype.card k - 1) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (Fintype.card (ConfigurationGroup σ)) hfactor
  exact hle.trans (card_groups_mul_sub_one_le σ)

theorem groupSelectionData_direction_multiplicity_le_two
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (d : Direction F) :
    (Finset.univ.filter (fun i => d ∈ (groupSelectionData σ u v huv).dirs i)).card ≤ 2 := by
  classical
  let e := Fintype.equivFin (ConfigurationGroup σ)
  let I := Finset.univ.filter (fun i => d ∈ (groupSelectionData σ u v huv).dirs i)
  let J := Finset.univ.filter (fun i => d ∈ groupConflict σ u v huv i)
  have hsub : I.image e.symm ⊆ J := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e.symm.injective] at hc
  exact hc.trans (groupConflict_multiplicity_le_two σ u v huv d)

theorem groupSelectionData_bounded (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hs : 2 ≤ Fintype.card k) :
    Selection.Bounded (groupSelectionConstant (Fintype.card k))
      (groupSelectionData σ u v huv) := by
  classical
  have htwo : 2 ≤ groupSelectionConstant (Fintype.card k) := by
    unfold groupSelectionConstant
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (card_groups_le_two_mul_card σ hs).trans
      (Nat.mul_le_mul_right (Fintype.card F) htwo)
  · intro i
    change (groupPoints σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)).card ≤ _
    rw [groupPoints_card]
    unfold groupSelectionConstant
    omega
  · intro i
    have hc := groupConflict_card_le σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)
    change (groupConflict σ u v huv
      ((Fintype.equivFin (ConfigurationGroup σ)).symm i)).card ≤ _
    unfold groupSelectionConstant
    omega
  · intro d
    exact (groupSelectionData_direction_multiplicity_le_two σ u v huv d).trans htwo

def selectedShifts (σ : k →+* F) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (i : ConfigurationGroup σ) : Point F :=
  pool ((Fintype.equivFin (ConfigurationGroup σ)) i,
    choice ((Fintype.equivFin (ConfigurationGroup σ)) i))

theorem selectedShifts_projection_ne
    (σ : k →+* F) (u v : k) (huv : u ≠ v) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (hchoice : ∀ i j, i ≠ j →
      ¬ Selection.Conflict (groupSelectionData σ u v huv) i j
        (pool (i, choice i)) (pool (j, choice j)))
    (i j : ConfigurationGroup σ) (hij : i ≠ j)
    (x y : Point k) (d : Direction F)
    (hd : d ∈ groupConflict σ u v huv i ∪ groupConflict σ u v huv j) :
    projection d (placedPoint σ (groupPlacement σ u v huv i)
        (selectedShifts σ pool choice i) x) ≠
      projection d (placedPoint σ (groupPlacement σ u v huv j)
        (selectedShifts σ pool choice j) y) := by
  classical
  let e := Fintype.equivFin (ConfigurationGroup σ)
  intro heq
  apply hchoice (e i) (e j) (fun h => hij (e.injective h))
  refine ⟨(groupPlacement σ u v huv i).apply (mapPoint σ x), ?_,
    (groupPlacement σ u v huv j).apply (mapPoint σ y), ?_, d, ?_, ?_⟩
  · change (groupPlacement σ u v huv i).apply (mapPoint σ x) ∈
      groupPoints σ u v huv (e.symm (e i))
    rw [e.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · change (groupPlacement σ u v huv j).apply (mapPoint σ y) ∈
      groupPoints σ u v huv (e.symm (e j))
    rw [e.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  · change d ∈ groupConflict σ u v huv (e.symm (e i)) ∪
      groupConflict σ u v huv (e.symm (e j))
    simpa only [e.symm_apply_apply] using hd
  · rw [Selection.projection_sub_eq]
    exact sub_eq_zero.mpr (by
      simpa only [placedPoint, selectedShifts, e] using heq)

theorem selectedShifts_deletionSeparated
    (σ : k →+* F) (u v : k) (huv : u ≠ v) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (hchoice : ∀ i j, i ≠ j →
      ¬ Selection.Conflict (groupSelectionData σ u v huv) i j
        (pool (i, choice i)) (pool (j, choice j)))
    (a : GadgetOutcome k) :
    DeletionSeparated σ (groupPlacement σ u v huv) (selectedShifts σ pool choice) a := by
  classical
  intro i j hij p hp q hq d hd
  obtain ⟨x, rfl⟩ :=
    (mem_placedSubplane_iff σ (groupPlacement σ u v huv i)
      (selectedShifts σ pool choice i) p).mp hp
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
  apply selectedShifts_projection_ne σ u v huv pool choice hchoice i j hij x y d
  exact Finset.mem_union_right _ (groupAltered_subset_conflict σ u v huv j hd)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.Construction

def thinFailureConstant (s K : ℕ) : ℝ := 128 * (K : ℝ) ^ 6 * (s : ℝ) ^ 12

theorem thinFailureBound_le (s K N : ℕ) {q : ℝ} (hq : 1 ≤ q)
    (hN : (N : ℝ) * (s - 1 : ℕ) ≤ 2 * q) :
    q ^ 3 * (q + 1) * (N : ℝ) ^ 6 *
        ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2) ^ 6 ≤
      thinFailureConstant s K / q ^ 2 := by
  have hqpos : 0 < q := by linarith
  have hqne : q ≠ 0 := hqpos.ne'
  have hbase : (N : ℝ) * ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2) ≤
      2 * (K : ℝ) * (s : ℝ) ^ 2 / q := by
    calc
      _ = (K : ℝ) * (s : ℝ) ^ 2 * ((N : ℝ) * (s - 1 : ℕ)) / q ^ 2 := by
        push_cast
        ring
      _ ≤ (K : ℝ) * (s : ℝ) ^ 2 * (2 * q) / q ^ 2 := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hN (by positivity)
        · positivity
      _ = 2 * (K : ℝ) * (s : ℝ) ^ 2 / q := by
        field_simp [hqne]
  have hfactor : q ^ 3 * (q + 1) ≤ 2 * q ^ 4 := by
    calc
      _ ≤ q ^ 3 * (2 * q) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * q ^ 4 := by ring
  calc
    _ = q ^ 3 * (q + 1) *
        ((N : ℝ) * ((K : ℝ) * (s ^ 2 : ℕ) * (s - 1 : ℕ) / q ^ 2)) ^ 6 := by
      rw [mul_pow]
      ring
    _ ≤ q ^ 3 * (q + 1) * (2 * (K : ℝ) * (s : ℝ) ^ 2 / q) ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase 6) (by positivity)
    _ ≤ 2 * q ^ 4 * (2 * (K : ℝ) * (s : ℝ) ^ 2 / q) ^ 6 :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = thinFailureConstant s K / q ^ 2 := by
      unfold thinFailureConstant
      field_simp [hqne]
      ring

theorem tendsto_thinFailureBound (s K : ℕ) :
    Tendsto (fun q : ℕ => thinFailureConstant s K / (q : ℝ) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun q : ℝ => thinFailureConstant s K / q ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  exact h.comp tendsto_natCast_atTop_atTop

theorem exists_thinFailure_cutoff (s K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → thinFailureConstant s K / (q : ℝ) ^ 2 ≤ η := by
  exact Filter.eventually_atTop.mp ((tendsto_thinFailureBound s K).eventually_le_const hη)

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
variable [DecidableEq k] [DecidableEq F]

theorem prob_groupPoolThin_ge (σ : k →+* F) (u v : k) (huv : u ≠ v) (K : ℕ) :
    1 - thinFailureConstant (Fintype.card k) K / (Fintype.card F : ℝ) ^ 2 ≤
      (poolThinLaw (F := F) (ConfigurationGroup σ) K).prob
        (PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv)) := by
  have hraw := prob_not_poolThin_le (K := K)
    (groupPoints σ u v huv) (groupAltered σ u v huv)
    (Fintype.card k ^ 2) (Fintype.card k - 1)
    (fun i => le_of_eq (groupPoints_card σ u v huv i))
    (fun i => le_of_eq (groupAltered_card σ u v huv i))
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := F)))
  have hN : (Fintype.card (ConfigurationGroup σ) : ℝ) * (Fintype.card k - 1 : ℕ) ≤
      2 * (Fintype.card F : ℝ) := by
    exact_mod_cast card_groups_mul_sub_one_le σ
  have hbound := hraw.trans
    (thinFailureBound_le (Fintype.card k) K (Fintype.card (ConfigurationGroup σ)) hq hN)
  rw [FiniteLaw.prob_compl] at hbound
  linarith

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

universe u

namespace RyserCoveringCounterexample.Selection

alias compatible_selection_uniform := compatible_selection_uniform_oddExt

end RyserCoveringCounterexample.Selection

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

universe uk uf

variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]

def GoodAmbientPool {F : Type uf} [Field F] [Fintype F] [DecidableEq F]
    (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (pool : AmbientPool σ K) : Prop :=
  Selection.HasCompatibleChoice (groupSelectionData σ u v huv)
      (ambientFlatPoolEquiv σ K pool) ∧
    LineCover.GoodLineCover (ambientDeletionDelta (Fintype.card k) K)
      (ambientDeletionDelta (Fintype.card k) K / 10)
      (ambientPoolConfig σ u v huv a ha K pool) ∧
    PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv) pool

theorem exists_goodAmbientPool_uniform
    (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (hs : 2 ≤ Fintype.card k) :
    ∃ K Q : ℕ, 6 ≤ K ∧
      ∀ (F : Type uf) [Field F] [Fintype F] [DecidableEq F] (σ : k →+* F),
        Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
        (1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
          ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) ∧
        ∃ pool : AmbientPool σ K, GoodAmbientPool σ u v huv a ha K pool := by
  classical
  let s := Fintype.card k
  let D := groupSelectionConstant s
  have hD : 1 ≤ D := by dsimp [D, groupSelectionConstant]; omega
  obtain ⟨K, hK, hselection⟩ := Selection.compatible_selection_uniform.{uf} D hD
  obtain ⟨QS, hQS⟩ := hselection (1 / 4) (by norm_num)
  let δ := ambientDeletionDelta s K
  let ρ := δ / 10
  let DA := ambientDeletionConstant s K
  have hδ : 0 < δ := ambientDeletionDelta_pos s K
  have hρ : 0 < ρ := div_pos hδ (by norm_num)
  have hDA : 0 < DA := lt_of_lt_of_le (by decide : 0 < 2)
    (ambientDeletionConstant_two_le s K)
  obtain ⟨QL, hQL⟩ := LineCover.uniform_linecover_probability.{uf}
    DA δ ρ hDA hδ hρ (1 / 4) (by norm_num)
  obtain ⟨QT, hQT⟩ := exists_thinFailure_cutoff s K (η := 1 / 4) (by norm_num)
  let QF : ℕ := ⌈10 / δ⌉₊ + 1
  refine ⟨K, QS + QL + QT + 2 * (s - 1) ^ 2 + QF, hK, ?_⟩
  intro F instField instFintype instDecidable σ hq hsub
  have hqS : QS ≤ Fintype.card F := by omega
  have hqL : QL ≤ Fintype.card F := by omega
  have hqT : QT ≤ Fintype.card F := by omega
  have hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F := by
    change 2 * (s - 1) ^ 2 ≤ Fintype.card F
    omega
  have hqF : QF ≤ Fintype.card F := by omega
  have hqFreal : (QF : ℝ) ≤ Fintype.card F := by exact_mod_cast hqF
  have hforce : 1 + ρ * Fintype.card F < δ * Fintype.card F / 2 := by
    have hceil : 10 / δ ≤ (⌈10 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hlarge : 10 / δ < (Fintype.card F : ℝ) := by
      dsimp [QF] at hqFreal
      push_cast at hqFreal
      linarith
    have hproduct : 10 < (Fintype.card F : ℝ) * δ := (div_lt_iff₀ hδ).mp hlarge
    dsimp [ρ]
    nlinarith
  refine ⟨hforce, ?_⟩
  let μ := poolThinLaw (F := F) (ConfigurationGroup σ) K
  let Selected : AmbientPool σ K → Prop := fun pool =>
    Selection.HasCompatibleChoice (groupSelectionData σ u v huv)
      (ambientFlatPoolEquiv σ K pool)
  let Rigid : AmbientPool σ K → Prop := fun pool =>
    LineCover.GoodLineCover δ ρ (ambientPoolConfig σ u v huv a ha K pool)
  let Thin : AmbientPool σ K → Prop :=
    PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv)
  have hselect : 1 - (1 / 4 : ℝ) ≤ μ.prob Selected := by
    have h := hQS F (Fintype.card (ConfigurationGroup σ)) (groupSelectionData σ u v huv)
      (groupSelectionData_bounded σ u v huv hs) hqS
    rw [← poolThinLaw_map_ambientFlatPoolEquiv σ K, FiniteLaw.prob_map] at h
    exact h
  have hrigid : 1 - (1 / 4 : ℝ) ≤ μ.prob Rigid := by
    have h := hQL F hqL hsub (ambientDeletionProcess σ u v huv a ha K hs hsmall)
    change 1 - (1 / 4 : ℝ) ≤ (FiniteLaw.pi (ambientTrials σ u v huv a ha K)).prob
      (LineCover.GoodLineCover δ ρ) at h
    rw [← poolThinLaw_map_ambientPoolConfig σ u v huv a ha K, FiniteLaw.prob_map] at h
    exact h
  have hthin : 1 - (1 / 4 : ℝ) ≤ μ.prob Thin := by
    have h := prob_groupPoolThin_ge σ u v huv K
    have htail := hQT (Fintype.card F) hqT
    exact (sub_le_sub_left htail 1).trans h
  have hex : ∃ pool : AmbientPool σ K, Selected pool ∧ Rigid pool ∧ Thin pool := by
    by_contra hnot
    have himp : ∀ pool, Selected pool → ¬ Rigid pool ∨ ¬ Thin pool := by
      intro pool hselected
      by_cases hr : Rigid pool
      · exact Or.inr (fun ht => hnot ⟨pool, hselected, hr, ht⟩)
      · exact Or.inl hr
    have hmono := (μ.prob_mono himp).trans (μ.prob_union_le (fun pool => ¬ Rigid pool)
      (fun pool => ¬ Thin pool))
    rw [μ.prob_compl, μ.prob_compl] at hmono
    linarith
  obtain ⟨pool, hselected, hrigid', hthin'⟩ := hex
  exact ⟨pool, hselected, hrigid', hthin'⟩

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

def ambientPoolDeletedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K) : Finset (AffineLine F) :=
  Finset.univ.biUnion (fun i => Finset.univ.biUnion
    (fun j => deletedLines σ (groupPlacement σ u v huv i) (b i j) a))

@[simp] theorem mem_ambientPoolDeletedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K) (l : AffineLine F) :
    l ∈ ambientPoolDeletedLines σ u v huv a K b ↔
      ∃ i j, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i j) a := by
  simp only [ambientPoolDeletedLines, Finset.mem_biUnion, Finset.mem_univ, true_and]

def ambientSelectedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) : Finset (AffineLine F) :=
  allDeletedLines σ (groupPlacement σ u v huv) (fun i => b i (choice i)) a

@[simp] theorem mem_ambientSelectedLines (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (l : AffineLine F) :
    l ∈ ambientSelectedLines σ u v huv a K b choice ↔
      ∃ i, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i (choice i)) a :=
  mem_allDeletedLines σ (groupPlacement σ u v huv) (fun i => b i (choice i)) a l

def ambientSelectedSurvivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) : Finset (Point F) :=
  Finset.univ \ (ambientSelectedLines σ u v huv a K b choice).biUnion linePoints

theorem mem_ambientSelectedSurvivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (x : Point F) :
    x ∈ ambientSelectedSurvivors σ u v huv a K b choice ↔
      ∀ l ∈ ambientSelectedLines σ u v huv a K b choice, ¬Incidence x l := by
  constructor
  · intro hx l hl hxl
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
      ⟨l, hl, (mem_linePoints x l).mpr hxl⟩)
  · intro hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro h
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp h
    exact hx l hl ((mem_linePoints x l).mp hxl)

theorem mem_survivors_ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (ignore : Finset (Finset (Point F))) (x : Point F) :
    x ∈ LineCover.survivors ignore (ambientPoolConfig σ u v huv a ha K b) ↔
      ∀ i j l, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i j) a →
        linePoints l ∉ ignore → ¬Incidence x l := by
  constructor
  · intro hx i j l hl hi hxl
    have ht := LineCover.mem_survivors.mp hx
      ((Fintype.equivFin (AmbientPosition σ K)) (i, j))
    rw [ambientPoolConfig_at] at ht
    apply ht
    exact (mem_deleted_ambientLineOutcome _ _ ignore x).mpr ⟨l, hl, hi, hxl⟩
  · intro h
    apply LineCover.mem_survivors.mpr
    intro t hx
    change x ∈ LineCover.deleted ignore
      (ambientTrialOutcome σ (groupPlacement σ u v huv (ambientPosition σ K t).1)
        a ha K (b (ambientPosition σ K t).1 (ambientPosition σ K t).2)) at hx
    rw [ambientTrialOutcome, mem_deleted_ambientLineOutcome] at hx
    obtain ⟨l, hl, hi, hxl⟩ := hx
    exact h (ambientPosition σ K t).1 (ambientPosition σ K t).2 l hl hi hxl

theorem ambientPool_survivors_subset_selected (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) :
    LineCover.survivors ∅ (ambientPoolConfig σ u v huv a ha K b) ⊆
      ambientSelectedSurvivors σ u v huv a K b choice := by
  intro x hx
  apply (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mpr
  intro l hl
  obtain ⟨i, hi⟩ := (mem_ambientSelectedLines σ u v huv a K b choice l).mp hl
  exact (mem_survivors_ambientPoolConfig σ u v huv a ha K b ∅ x).mp hx
    i (choice i) l hi (by simp)

theorem ambientPool_ignored_survivors_subset_selected (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (ell : AffineLine F) (hell : ell ∉ ambientSelectedLines σ u v huv a K b choice) :
    LineCover.survivors {linePoints ell} (ambientPoolConfig σ u v huv a ha K b) ⊆
      ambientSelectedSurvivors σ u v huv a K b choice := by
  intro x hx
  apply (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mpr
  intro l hl
  obtain ⟨i, hi⟩ := (mem_ambientSelectedLines σ u v huv a K b choice l).mp hl
  apply (mem_survivors_ambientPoolConfig σ u v huv a ha K b {linePoints ell} x).mp hx
    i (choice i) l hi
  intro hignore
  have heq : l = ell := ambient_linePoints_injective (Finset.mem_singleton.mp hignore)
  exact hell (heq ▸ hl)

theorem ambientPool_goodLineCover_selected (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (δ ρ : ℝ)
    (hgood : LineCover.GoodLineCover δ ρ (ambientPoolConfig σ u v huv a ha K b)) :
    (∀ ell, ell ∉ ambientSelectedLines σ u v huv a K b choice →
      δ * Fintype.card F / 2 ≤
        ((ambientSelectedSurvivors σ u v huv a K b choice ∩ linePoints ell).card : ℝ)) ∧
    (∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      ambientSelectedSurvivors σ u v huv a K b choice ⊆ L.biUnion linePoints →
      ∃ p : ProjectivePoint F,
        (1 - ρ) * Fintype.card F ≤ ((LineCover.coverPencil L p).card : ℝ)) := by
  constructor
  · intro ell hell
    apply (hgood.1 ell).trans
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter
      (ambientPool_ignored_survivors_subset_selected σ u v huv a ha K b choice ell hell)
      (Finset.Subset.refl _))
  · intro L hL hcover
    apply hgood.2 L hL
    have hsub := (ambientPool_survivors_subset_selected σ u v huv a ha K b choice).trans hcover
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty]
    exact Nat.zero_le _

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

structure ConfigurationData (k F G : Type*) [DecidableEq F] where
  altered : G → Finset (Direction F)
  inverseSlope : ∀ i, {d : Direction F // d ∈ altered i} → k
  base : G → Point k → Point F
  transform : Point k → Point k
  retained : Finset (Point k)
  ordinaryPoints : Finset (Point F)

abbrev Vertex {k F G : Type*} [DecidableEq F]
    (altered : G → Finset (Direction F)) :=
  AffineLine F ⊕ (Σ i : G, {d : Direction F // d ∈ altered i} × k)

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

def ordinaryVertex (data : ConfigurationData k F G) (ell : AffineLine F) :
    Vertex (k := k) data.altered := Sum.inl ell

def specialVertex (data : ConfigurationData k F G) (i : G)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    Vertex (k := k) data.altered := Sum.inr ⟨i, (d, c)⟩

def vertexPart (data : ConfigurationData k F G) :
    Vertex (k := k) data.altered → Direction F
  | Sum.inl ell => ell.1
  | Sum.inr v => v.2.1.val

@[simp] theorem vertexPart_ordinaryVertex (data : ConfigurationData k F G)
    (ell : AffineLine F) : vertexPart data (ordinaryVertex data ell) = ell.1 := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; rfl

@[simp] theorem vertexPart_specialVertex (data : ConfigurationData k F G) (i : G)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    vertexPart data (specialVertex data i d c) = d.val := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; rfl

def exceptionalVertex (data : ConfigurationData k F G) (i : G) (w : Point k)
    (d : Direction F) : Vertex (k := k) data.altered :=
  if h : d ∈ data.altered i then
    specialVertex data i ⟨d, h⟩
      (projection (some (data.inverseSlope i ⟨d, h⟩)) (data.transform w))
  else ordinaryVertex data (lineThrough d (data.base i w))

theorem exceptionalVertex_of_mem (data : ConfigurationData k F G) (i : G)
    (w : Point k) (d : Direction F) (hd : d ∈ data.altered i) :
    exceptionalVertex data i w d = specialVertex data i ⟨d, hd⟩
      (projection (some (data.inverseSlope i ⟨d, hd⟩)) (data.transform w)) := let _ := instDecidableEqk; let _ := instDecidableEqG; by
  simp only [exceptionalVertex, dite_eq_left hd]

theorem exceptionalVertex_of_notMem (data : ConfigurationData k F G) (i : G)
    (w : Point k) (d : Direction F) (hd : d ∉ data.altered i) :
    exceptionalVertex data i w d = ordinaryVertex data (lineThrough d (data.base i w)) := let _ := instDecidableEqk; let _ := instDecidableEqG; by
  simp only [exceptionalVertex, dite_eq_right hd]

@[simp] theorem vertexPart_exceptionalVertex (data : ConfigurationData k F G)
    (i : G) (w : Point k) (d : Direction F) :
    vertexPart data (exceptionalVertex data i w d) = d := by
  by_cases hd : d ∈ data.altered i
  · rw [exceptionalVertex_of_mem data i w d hd]
    rfl
  · rw [exceptionalVertex_of_notMem data i w d hd]
    rfl

variable [Fintype F]

def ordinaryEdge (data : ConfigurationData k F G) (x : Point F) :
    Finset (Vertex (k := k) data.altered) :=
  Finset.univ.image (fun d => ordinaryVertex data (lineThrough d x))

def exceptionalEdge (data : ConfigurationData k F G) (i : G) (w : Point k) :
    Finset (Vertex (k := k) data.altered) :=
  Finset.univ.image (exceptionalVertex data i w)

theorem ordinaryVertex_mem_ordinaryEdge (data : ConfigurationData k F G)
    (x : Point F) (d : Direction F) :
    ordinaryVertex data (lineThrough d x) ∈ ordinaryEdge data x := let _ := instFieldk;
  Finset.mem_image_of_mem _ (Finset.mem_univ d)

theorem selector_edge_partite {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (part : V → I) (selector : I → V)
    (hpart : ∀ i, part (selector i) = i) :
    ∀ i, ∃! v, v ∈ Finset.univ.image selector ∧ part v = i := by
  intro i
  refine ⟨selector i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hpart i⟩, ?_⟩
  rintro v ⟨hv, hvi⟩
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  rw [hpart j] at hvi
  exact congrArg selector hvi

theorem mem_selector_edge_iff {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (part : V → I) (selector : I → V)
    (hpart : ∀ i, part (selector i) = i) (v : V) :
    v ∈ Finset.univ.image selector ↔ v = selector (part v) := by
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    rw [hpart i]
  · intro hv
    rw [hv]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem ordinaryEdge_partite (data : ConfigurationData k F G) (x : Point F) :
    ∀ d, ∃! v, v ∈ ordinaryEdge data x ∧ vertexPart data v = d := let _ := instFieldk;
  selector_edge_partite (vertexPart data)
    (fun d => ordinaryVertex data (lineThrough d x)) (fun _ => rfl)

theorem exceptionalEdge_partite (data : ConfigurationData k F G) (i : G)
    (w : Point k) :
    ∀ d, ∃! v, v ∈ exceptionalEdge data i w ∧ vertexPart data v = d :=
  selector_edge_partite (vertexPart data) (exceptionalVertex data i w)
    (vertexPart_exceptionalVertex data i w)

theorem mem_exceptionalEdge_iff (data : ConfigurationData k F G) (i : G)
    (w : Point k) (v : Vertex (k := k) data.altered) :
    v ∈ exceptionalEdge data i w ↔
      v = exceptionalVertex data i w (vertexPart data v) :=
  mem_selector_edge_iff (vertexPart data) (exceptionalVertex data i w)
    (vertexPart_exceptionalVertex data i w) v

variable [Fintype G]

def hypergraph (data : ConfigurationData k F G) :
    Hypergraph (Vertex (k := k) data.altered) := by
  classical
  exact data.ordinaryPoints.image (ordinaryEdge data) ∪
    Finset.univ.biUnion (fun i => data.retained.image (exceptionalEdge data i))

@[simp] theorem mem_hypergraph (data : ConfigurationData k F G)
    (e : Finset (Vertex (k := k) data.altered)) :
    e ∈ hypergraph data ↔
      (∃ x ∈ data.ordinaryPoints, ordinaryEdge data x = e) ∨
      (∃ i, ∃ w ∈ data.retained, exceptionalEdge data i w = e) := by
  classical
  simp only [hypergraph, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_univ, true_and]

theorem hypergraph_partite (data : ConfigurationData k F G) :
    PartiteUniform (vertexPart data) (hypergraph data) := by
  intro e he
  rcases (mem_hypergraph data e).mp he with ⟨x, _, rfl⟩ | ⟨i, w, _, rfl⟩
  · exact ordinaryEdge_partite data x
  · exact exceptionalEdge_partite data i w

theorem hypergraph_rPartiteUniform (data : ConfigurationData k F G) :
    RPartiteUniform (Fintype.card F + 1) (hypergraph data) := by
  simpa only [Fintype.card_option] using (hypergraph_partite data).rPartiteUniform

theorem hypergraph_nonempty (data : ConfigurationData k F G) (i : G)
    (hY : data.retained.Nonempty) : (hypergraph data).Nonempty := by
  obtain ⟨w, hw⟩ := hY
  refine ⟨exceptionalEdge data i w, (mem_hypergraph data _).mpr ?_⟩
  exact Or.inr ⟨i, w, hw, rfl⟩

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

theorem ordinaryVertex_mem_ordinaryEdge_iff (data : ConfigurationData k F G)
    (x : Point F) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ ordinaryEdge data x ↔ Incidence x ell := by
  constructor
  · intro hv
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hv
    have hline : lineThrough d x = ell := Sum.inl.inj hd
    rw [← hline]
    exact incidence_lineThrough d x
  · intro hinc
    rw [eq_lineThrough_of_incidence hinc]
    exact ordinaryVertex_mem_ordinaryEdge data x ell.1

theorem ordinaryVertex_mem_exceptionalEdge_iff (data : ConfigurationData k F G)
    (i : G) (w : Point k) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ exceptionalEdge data i w ↔
      ell.1 ∉ data.altered i ∧ Incidence (data.base i w) ell := by
  rw [mem_exceptionalEdge_iff data i w, vertexPart_ordinaryVertex]
  by_cases hd : ell.1 ∈ data.altered i
  · rw [exceptionalVertex_of_mem data i w ell.1 hd]
    constructor
    · intro hlabel
      simp [ordinaryVertex, specialVertex] at hlabel
    · intro h
      exact False.elim (h.1 hd)
  · rw [exceptionalVertex_of_notMem data i w ell.1 hd]
    constructor
    · intro hlabel
      have hline : ell = lineThrough ell.1 (data.base i w) := Sum.inl.inj hlabel
      exact ⟨hd, (congrArg Prod.snd hline).symm⟩
    · rintro ⟨_, hinc⟩
      exact congrArg (ordinaryVertex data) (eq_lineThrough_of_incidence hinc)

theorem specialVertex_mem_exceptionalEdge_iff (data : ConfigurationData k F G)
    (i : G) (w : Point k)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    specialVertex data i d c ∈ exceptionalEdge data i w ↔
      Incidence (data.transform w) (some (data.inverseSlope i d), c) := by
  rw [mem_exceptionalEdge_iff data i w, vertexPart_specialVertex,
    exceptionalVertex_of_mem data i w d.val d.property]
  change specialVertex data i d c =
      specialVertex data i d
        (projection (some (data.inverseSlope i d)) (data.transform w)) ↔
    Incidence (data.transform w) (some (data.inverseSlope i d), c)
  constructor
  · intro hlabel
    have hc : c = projection (some (data.inverseSlope i d)) (data.transform w) :=
      congrArg
        (fun v : Σ j : G, {e : Direction F // e ∈ data.altered j} × k => v.2.2)
        (Sum.inr.inj hlabel)
    exact hc.symm
  · intro hinc
    change projection (some (data.inverseSlope i d)) (data.transform w) = c at hinc
    rw [hinc]

theorem specialVertex_notMem_exceptionalEdge_of_ne (data : ConfigurationData k F G)
    (i j : G) (hij : i ≠ j) (w : Point k)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    specialVertex data i d c ∉ exceptionalEdge data j w := by
  intro hv
  have hlabel := (mem_exceptionalEdge_iff data j w _).mp hv
  rw [vertexPart_specialVertex] at hlabel
  by_cases hd : d.val ∈ data.altered j
  · rw [exceptionalVertex_of_mem data j w d.val hd] at hlabel
    exact hij (congrArg Sigma.fst (Sum.inr.inj hlabel))
  · rw [exceptionalVertex_of_notMem data j w d.val hd] at hlabel
    simp [ordinaryVertex, specialVertex] at hlabel

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

private theorem exists_equal_projection {K : Type*} [Field K] [DecidableEq K]
    (p q : Point K) : ∃ d : Direction K, projection d p = projection d q := by
  refine ⟨(joinLine p q).1, ?_⟩
  have hp : projection (joinLine p q).1 p = (joinLine p q).2 :=
    incidence_joinLine_left p q
  have hq : projection (joinLine p q).1 q = (joinLine p q).2 :=
    incidence_joinLine_right p q
  exact hp.trans hq.symm

theorem ordinaryEdge_inter_ordinaryEdge (data : ConfigurationData k F G)
    (x y : Point F) : (ordinaryEdge data x ∩ ordinaryEdge data y).Nonempty := by
  refine ⟨ordinaryVertex data (joinLine x y), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (ordinaryVertex_mem_ordinaryEdge_iff data x _).2
      (incidence_joinLine_left x y)
  · exact (ordinaryVertex_mem_ordinaryEdge_iff data y _).2
      (incidence_joinLine_right x y)

theorem exceptionalEdge_inter_of_projection_eq (data : ConfigurationData k F G)
    (i j : G) (w z : Point k) (d : Direction F)
    (hi : d ∉ data.altered i) (hj : d ∉ data.altered j)
    (heq : projection d (data.base i w) = projection d (data.base j z)) :
    (exceptionalEdge data i w ∩ exceptionalEdge data j z).Nonempty := by
  refine ⟨ordinaryVertex data (lineThrough d (data.base i w)),
    Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data i w _).2 ⟨hi, rfl⟩
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data j z _).2 ⟨hj, heq.symm⟩

theorem ordinaryEdge_inter_exceptionalEdge (data : ConfigurationData k F G)
    (x : Point F) (i : G) (w : Point k)
    (havoid : ∀ d ∈ data.altered i,
      projection d x ≠ projection d (data.base i w)) :
    (ordinaryEdge data x ∩ exceptionalEdge data i w).Nonempty := by
  obtain ⟨d, hd⟩ := exists_equal_projection x (data.base i w)
  have hnot : d ∉ data.altered i := fun hm => havoid d hm hd
  refine ⟨ordinaryVertex data (lineThrough d x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact ordinaryVertex_mem_ordinaryEdge data x d
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data i w _).2 ⟨hnot, hd.symm⟩

theorem exceptionalEdge_inter_of_separated (data : ConfigurationData k F G)
    (i j : G) (w z : Point k)
    (hi : ∀ d ∈ data.altered i,
      projection d (data.base i w) ≠ projection d (data.base j z))
    (hj : ∀ d ∈ data.altered j,
      projection d (data.base j z) ≠ projection d (data.base i w)) :
    (exceptionalEdge data i w ∩ exceptionalEdge data j z).Nonempty := by
  obtain ⟨d, hd⟩ := exists_equal_projection (data.base i w) (data.base j z)
  exact exceptionalEdge_inter_of_projection_eq data i j w z d
    (fun hm => hi d hm hd) (fun hm => hj d hm hd.symm) hd

theorem exceptionalEdge_inter_sameGroup (data : ConfigurationData k F G) (i : G)
    (directions : Direction k → Direction F)
    (hmem : ∀ t : k, t ≠ 0 → directions (some t) ∈ data.altered i)
    (hinverse : ∀ (t : k) (ht : t ≠ 0),
      data.inverseSlope i ⟨directions (some t), hmem t ht⟩ = t)
    (haxisOutside : ∀ a : Direction k, a = none ∨ a = some 0 →
      directions a ∉ data.altered i)
    (haxisTransport : ∀ a : Direction k, a = none ∨ a = some 0 →
      ∀ p q : Point k,
        projection a (data.transform p) = projection a (data.transform q) →
        projection (directions a) (data.base i p) =
          projection (directions a) (data.base i q))
    (w z : Point k) :
    (exceptionalEdge data i w ∩ exceptionalEdge data i z).Nonempty := by
  obtain ⟨a, ha⟩ := exists_equal_projection (data.transform w) (data.transform z)
  cases a with
  | none =>
      exact exceptionalEdge_inter_of_projection_eq data i i w z (directions none)
        (haxisOutside none (Or.inl rfl)) (haxisOutside none (Or.inl rfl))
        (haxisTransport none (Or.inl rfl) w z ha)
  | some t =>
      by_cases ht : t = 0
      · subst t
        exact exceptionalEdge_inter_of_projection_eq data i i w z (directions (some 0))
          (haxisOutside (some 0) (Or.inr rfl))
          (haxisOutside (some 0) (Or.inr rfl))
          (haxisTransport (some 0) (Or.inr rfl) w z ha)
      · let d : {d : Direction F // d ∈ data.altered i} :=
          ⟨directions (some t), hmem t ht⟩
        have hinv : data.inverseSlope i d = t := hinverse t ht
        let c := projection (some (data.inverseSlope i d)) (data.transform w)
        refine ⟨specialVertex data i d c, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · exact (specialVertex_mem_exceptionalEdge_iff data i w d c).2 rfl
        · apply (specialVertex_mem_exceptionalEdge_iff data i z d c).2
          change projection (some (data.inverseSlope i d)) (data.transform z) =
            projection (some (data.inverseSlope i d)) (data.transform w)
          rw [hinv]
          exact ha.symm

variable [Fintype G]

theorem hypergraph_intersecting_of_geometric_data (data : ConfigurationData k F G)
    (directions : G → Direction k → Direction F)
    (hmem : ∀ (i : G) (t : k), t ≠ 0 → directions i (some t) ∈ data.altered i)
    (hinverse : ∀ (i : G) (t : k) (ht : t ≠ 0),
      data.inverseSlope i ⟨directions i (some t), hmem i t ht⟩ = t)
    (haxisOutside : ∀ (i : G) (a : Direction k), a = none ∨ a = some 0 →
      directions i a ∉ data.altered i)
    (haxisTransport : ∀ (i : G) (a : Direction k), a = none ∨ a = some 0 →
      ∀ p q : Point k,
        projection a (data.transform p) = projection a (data.transform q) →
        projection (directions i a) (data.base i p) =
          projection (directions i a) (data.base i q))
    (havoid : ∀ x ∈ data.ordinaryPoints, ∀ i, ∀ w ∈ data.retained,
      ∀ d ∈ data.altered i, projection d x ≠ projection d (data.base i w))
    (hseparate : ∀ i j : G, i ≠ j → ∀ w ∈ data.retained, ∀ z ∈ data.retained,
      ∀ d ∈ data.altered i,
        projection d (data.base i w) ≠ projection d (data.base j z)) :
    Intersecting (hypergraph data) := by
  intro e he f hf _
  rcases (mem_hypergraph data e).mp he with ⟨x, hx, rfl⟩ | ⟨i, w, hw, rfl⟩
  · rcases (mem_hypergraph data f).mp hf with ⟨y, _, rfl⟩ | ⟨j, z, hz, rfl⟩
    · exact ordinaryEdge_inter_ordinaryEdge data x y
    · exact ordinaryEdge_inter_exceptionalEdge data x j z (havoid x hx j z hz)
  · rcases (mem_hypergraph data f).mp hf with ⟨y, hy, rfl⟩ | ⟨j, z, hz, rfl⟩
    · simpa only [Finset.inter_comm] using
        ordinaryEdge_inter_exceptionalEdge data y i w (havoid y hy i w hw)
    · by_cases hij : i = j
      · subst j
        exact exceptionalEdge_inter_sameGroup data i (directions i) (hmem i)
          (hinverse i) (haxisOutside i) (haxisTransport i) w z
      · exact exceptionalEdge_inter_of_separated data i j w z
          (hseparate i j hij w hw z hz) (hseparate j i (fun h => hij h.symm) z hz w hw)

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [instFintypek : Fintype k] [instDecidableEqk : DecidableEq k] [DecidableEq F] [DecidableEq G]

theorem projection_cubeMap_axis_eq_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0) (p q : Point k) :
    projection d (cubeMap p) = projection d (cubeMap q) ↔
      projection d p = projection d q := let _ := instDecidableEqk; by
  rcases hd with rfl | rfl
  · change p.1 ^ 3 = q.1 ^ 3 ↔ p.1 = q.1
    exact (cube_bijective hcop).injective.eq_iff
  · simp only [projection_some_zero, cubeMap]

theorem projection_placedPoint_cubeMap_axis_eq_iff
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0) (p q : Point k) :
    projection (placedDirection σ M d) (placedPoint σ M b p) =
        projection (placedDirection σ M d) (placedPoint σ M b q) ↔
      projection d (cubeMap p) = projection d (cubeMap q) :=
  (projection_placedPoint_eq_iff σ M b d p q).trans
    (projection_cubeMap_axis_eq_iff hcop d hd p q).symm

theorem cubeMap_incidence_axis_of_placed_incidence
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0)
    (ell : AffineLine F) (hell : ell.1 = placedDirection σ M d)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) :
    Incidence (cubeMap p) (lineThrough d (cubeMap q)) := by
  have hproj : projection ell.1 (placedPoint σ M b p) =
      projection ell.1 (placedPoint σ M b q) := hp.trans hq.symm
  rw [hell] at hproj
  exact (projection_placedPoint_cubeMap_axis_eq_iff σ M b hcop d hd p q).1 hproj

theorem placedPoint_eq_of_incidence_of_direction_outside
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (ell : AffineLine F)
    (houtside : ∀ d : Direction k, ell.1 ≠ placedDirection σ M d)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) : p = q := let _ := instFintypek; by
  let d := (joinLine p q).1
  have hsmall : projection d p = projection d q :=
    (incidence_joinLine_left p q).trans (incidence_joinLine_right p q).symm
  have hplaced := (projection_placedPoint_eq_iff σ M b d p q).2 hsmall
  have hell : projection ell.1 (placedPoint σ M b p) =
      projection ell.1 (placedPoint σ M b q) := hp.trans hq.symm
  apply placedPoint_injective σ M b
  exact point_eq_of_projection_eq_of_ne_direction (houtside d) hell hplaced

theorem placedPoint_eq_of_incidence_outside_altered_axis
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (ell : AffineLine F)
    (houtside : ell.1 ∉ alteredDirections σ M ∪ axisDirections σ M)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) : p = q := by
  apply placedPoint_eq_of_incidence_of_direction_outside σ M b ell ?_ p q hp hq
  intro d hd
  apply houtside
  rw [hd]
  exact placedDirection_mem_altered_or_axis σ M d

def placedConfiguration (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (Y : Finset (Point k)) (X : Finset (Point F)) :
    ConfigurationData k F G where
  altered i := alteredDirections σ (M i)
  inverseSlope i := alteredInverseSlope σ (M i)
  base i := placedPoint σ (M i) (b i)
  transform := cubeMap
  retained := Y
  ordinaryPoints := X

variable [Fintype F]

variable [Fintype G]

theorem placedHypergraph_intersecting
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (havoid : ∀ x ∈ X, ∀ i, ∀ w ∈ Y, ∀ d ∈ alteredDirections σ (M i),
      projection d x ≠ projection d (placedPoint σ (M i) (b i) w))
    (hseparate : ∀ i j : G, i ≠ j → ∀ w ∈ Y, ∀ z ∈ Y,
      ∀ d ∈ alteredDirections σ (M i),
        projection d (placedPoint σ (M i) (b i) w) ≠
          projection d (placedPoint σ (M j) (b j) z)) :
    Intersecting (hypergraph (placedConfiguration σ M b Y X)) := by
  exact hypergraph_intersecting_of_geometric_data (placedConfiguration σ M b Y X)
    (fun i => placedDirection σ (M i))
    (fun i => placedDirection_mem_alteredDirections σ (M i))
    (fun i => inverseSlope_placedDirection σ (M i))
    (fun i => placedDirection_axis_notMem_alteredDirections σ (M i))
    (fun i d hd p q hproj =>
      (projection_placedPoint_cubeMap_axis_eq_iff σ (M i) (b i)
        hcop d hd p q).2 hproj)
    havoid hseparate

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped Classical

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

theorem ambientSelectedSurvivors_projection_ne
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (x : Point F) (hx : x ∈ ambientSelectedSurvivors σ u v huv a K b choice)
    (i : ConfigurationGroup σ) (w : Point k) (hw : w ∈ retainedPoints a)
    (d : Direction F) (hd : d ∈ alteredDirections σ (groupPlacement σ u v huv i)) :
    projection d x ≠
      projection d (placedPoint σ (groupPlacement σ u v huv i) (b i (choice i)) w) := by
  intro hproj
  let ell := lineThrough d
    (placedPoint σ (groupPlacement σ u v huv i) (b i (choice i)) w)
  have hell : ell ∈ ambientSelectedLines σ u v huv a K b choice := by
    apply (mem_ambientSelectedLines σ u v huv a K b choice ell).mpr
    refine ⟨i, ?_⟩
    apply (mem_deletedLines σ (groupPlacement σ u v huv i) (b i (choice i)) a ell).mpr
    exact ⟨hd, w, hw, rfl⟩
  exact (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mp hx ell hell hproj

theorem DeletionSeparated.retained_projection_ne
    {G : Type*} [Fintype G] [DecidableEq G]
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i j : G) (hij : i ≠ j) (w : Point k) (hw : w ∈ retainedPoints a)
    (z : Point k) (d : Direction F) (hd : d ∈ alteredDirections σ (M i)) :
    projection d (placedPoint σ (M i) (b i) w) ≠
      projection d (placedPoint σ (M j) (b j) z) := by
  have hz : placedPoint σ (M j) (b j) z ∈ placedSubplane σ (M j) (b j) :=
    (mem_placedSubplane_iff σ (M j) (b j) _).mpr ⟨z, rfl⟩
  have hw' : placedPoint σ (M i) (b i) w ∈
      (retainedPoints a).image (placedPoint σ (M i) (b i)) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  exact (hsep j i (Ne.symm hij) _ hz _ hw' d hd).symm

def ambientSelectedConfiguration
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    ConfigurationData k F (ConfigurationGroup σ) :=
  placedConfiguration σ (groupPlacement σ u v huv) (fun i => b i (choice i))
    (retainedPoints a) (ambientSelectedSurvivors σ u v huv a K b choice)

theorem ambientSelectedHypergraph_intersecting
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hsep : DeletionSeparated σ (groupPlacement σ u v huv)
      (fun i => b i (choice i)) a) :
    Intersecting (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) := by
  apply placedHypergraph_intersecting σ (groupPlacement σ u v huv)
    (fun i => b i (choice i)) (retainedPoints a)
    (ambientSelectedSurvivors σ u v huv a K b choice) hcop
  · intro x hx i w hw d hd
    exact ambientSelectedSurvivors_projection_ne σ u v huv a K b choice x hx i w hw d hd
  · intro i j hij w hw z _ d hd
    exact DeletionSeparated.retained_projection_ne σ (groupPlacement σ u v huv)
      (fun i => b i (choice i)) a hsep i j hij w hw z d hd

theorem ambientSelectedHypergraph_nonempty
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (ha : GoodGadget a) :
    (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)).Nonempty := by
  exact hypergraph_nonempty (ambientSelectedConfiguration σ u v huv a K b choice)
    none ha.retained_nonempty

theorem ambientSelectedHypergraph_rPartiteUniform
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    RPartiteUniform (Fintype.card F + 1)
      (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) :=
  hypergraph_rPartiteUniform (ambientSelectedConfiguration σ u v huv a K b choice)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {G P : Type*}

theorem exists_selection_card_eq
    (I : Finset G) (W : G → Finset P) (n : ℕ)
    (hW : ∀ i ∈ I, n ≤ (W i).card) :
    ∃ S : G → Finset P,
      (∀ i ∈ I, S i ⊆ W i ∧ (S i).card = n) ∧
      (∀ i ∉ I, S i = ∅) := by
  classical
  have hchoose (i : G) (hi : i ∈ I) :
      ∃ T : Finset P, T ⊆ W i ∧ T.card = n :=
    Finset.exists_subset_card_eq (hW i hi)
  let S : G → Finset P := fun i =>
    if hi : i ∈ I then Classical.choose (hchoose i hi) else ∅
  refine ⟨S, ?_, ?_⟩
  · intro i hi
    simpa only [S, dite_eq_left hi] using Classical.choose_spec (hchoose i hi)
  · intro i hi
    simp only [S, dite_eq_right hi]

theorem exists_five_selection
    (I : Finset G) (W : G → Finset P)
    (hW : ∀ i ∈ I, 5 ≤ (W i).card) :
    ∃ S : G → Finset P,
      (∀ i ∈ I, S i ⊆ W i ∧ (S i).card = 5) ∧
      (∀ i ∉ I, S i = ∅) :=
  exists_selection_card_eq I W 5 hW

variable [DecidableEq G] [instDecidableEqP : DecidableEq P]

def selectedPositions (I : Finset G) (S : G → Finset P) : Finset (G × P) :=
  I.biUnion (fun i => (S i).image (fun w => (i, w)))

@[simp] theorem mem_selectedPositions
    {I : Finset G} {S : G → Finset P} {x : G × P} :
    x ∈ selectedPositions I S ↔ x.1 ∈ I ∧ x.2 ∈ S x.1 := by
  rcases x with ⟨i, w⟩
  simp [selectedPositions]

theorem card_selectedPositions_eq_sum (I : Finset G) (S : G → Finset P) :
    (selectedPositions I S).card = ∑ i ∈ I, (S i).card := by
  have hdisjoint : (I : Set G).PairwiseDisjoint
      (fun i => (S i).image (fun w => (i, w))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨w, _, hx⟩ := Finset.mem_image.mp hx
    obtain ⟨z, _, hy⟩ := Finset.mem_image.mp hy
    exact hij ((congrArg Prod.fst hx).trans (congrArg Prod.fst hy).symm)
  calc
    (selectedPositions I S).card =
        ∑ i ∈ I, ((S i).image (fun w => (i, w))).card :=
      Finset.card_biUnion hdisjoint
    _ = ∑ i ∈ I, (S i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.card_image_of_injective _
        (fun w z hwz => congrArg Prod.snd hwz)

theorem card_selectedPositions (I : Finset G) (S : G → Finset P) (n : ℕ)
    (hS : ∀ i ∈ I, (S i).card = n) :
    (selectedPositions I S).card = n * I.card := by
  calc
    (selectedPositions I S).card = ∑ i ∈ I, (S i).card :=
      card_selectedPositions_eq_sum I S
    _ = I.card * n := Finset.sum_const_nat hS
    _ = n * I.card := Nat.mul_comm _ _

theorem card_eq_card_image_fst_of_one_per_group
    (E : Finset (G × P))
    (hE : ∀ (i : G) (w z : P), (i, w) ∈ E → (i, z) ∈ E → w = z) :
    E.card = (E.image Prod.fst).card := let _ := instDecidableEqP; by
  symm
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  rcases x with ⟨i, w⟩
  rcases y with ⟨j, z⟩
  change i = j at hxy
  subst j
  exact congrArg (fun p : P => (i, p)) (hE i w z hx hy)

theorem card_le_selected_group_of_subset
    (I : Finset G) (S : G → Finset P) (E : Finset (G × P)) (i : G)
    (hE : E ⊆ selectedPositions I S)
    (hgroup : ∀ x ∈ E, x.1 = i) :
    E.card ≤ (S i).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    change x.2 ∈ S i
    have hs : x.2 ∈ S x.1 := (mem_selectedPositions.mp (hE hx)).2
    rw [hgroup x hx] at hs
    exact hs
  · intro x hx y hy hxy
    exact Prod.ext ((hgroup x hx).trans (hgroup y hy).symm) hxy

theorem card_le_five_of_subset_selectedPositions_one_group
    (I : Finset G) (S : G → Finset P) (E : Finset (G × P)) (i : G)
    (hE : E ⊆ selectedPositions I S)
    (hgroup : ∀ x ∈ E, x.1 = i)
    (hS : (S i).card ≤ 5) :
    E.card ≤ 5 :=
  (card_le_selected_group_of_subset I S E i hE hgroup).trans hS

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]
variable [instFintypeF : Fintype F] [instFintypeG : Fintype G]

def offPencilGroups (data : ConfigurationData k F G) (p : Point F)
    (ell : AffineLine F) : Finset G := by
  classical
  exact Finset.univ.filter (fun i => ∃ w ∈ data.retained,
    Incidence (data.base i w) ell ∧
      joinDirection p (data.base i w) ∈ data.altered i)

@[simp] theorem mem_offPencilGroups (data : ConfigurationData k F G)
    (p : Point F) (ell : AffineLine F) (i : G) :
    i ∈ offPencilGroups data p ell ↔ ∃ w ∈ data.retained,
      Incidence (data.base i w) ell ∧
        joinDirection p (data.base i w) ∈ data.altered i := let _ := instFieldk; let _ := instDecidableEqk; let _ := instDecidableEqG; let _ := instFintypeF; by
  classical
  simp only [offPencilGroups, Finset.mem_filter, Finset.mem_univ, true_and]

def OffPencilThin (data : ConfigurationData k F G) (p : Point F) : Prop :=
  ∀ ell : AffineLine F, ¬ Incidence p ell →
    (offPencilGroups data p ell).card ≤ 5

theorem joinDirection_mem_altered_of_incident_line
    (data : ConfigurationData k F G) (i : G) (p : Point F) (w : Point k)
    (ell : AffineLine F) (hne : p ≠ data.base i w)
    (hp : Incidence p ell) (hw : Incidence (data.base i w) ell)
    (hd : ell.1 ∈ data.altered i) :
    joinDirection p (data.base i w) ∈ data.altered i := let _ := instFieldk; let _ := instDecidableEqk; let _ := instDecidableEqG; let _ := instFintypeF; let _ := instFintypeG; by
  have hdir := congrArg Prod.fst (eq_joinLine_of_incidence hne hp hw)
  change ell.1 = joinDirection p (data.base i w) at hdir
  rw [← hdir]
  exact hd

theorem ordinaryVertex_notMem_exceptionalEdge_of_altered_join
    (data : ConfigurationData k F G) (p : Point F) (i : G) (w : Point k)
    (hne : p ≠ data.base i w)
    (hjoin : joinDirection p (data.base i w) ∈ data.altered i)
    (ell : AffineLine F) (hp : Incidence p ell) :
    ordinaryVertex data ell ∉ exceptionalEdge data i w := let _ := instFintypeG; by
  intro hhit
  obtain ⟨hunaltered, hw⟩ :=
    (ordinaryVertex_mem_exceptionalEdge_iff data i w ell).mp hhit
  have hdir := congrArg Prod.fst (eq_joinLine_of_incidence hne hp hw)
  change ell.1 = joinDirection p (data.base i w) at hdir
  apply hunaltered
  rw [hdir]
  exact hjoin

open scoped Classical

theorem selectedPositions_hit_card_le_five
    (data : ConfigurationData k F G) (p : Point F)
    (I : Finset G) (lines : G → AffineLine F) (S : G → Finset (Point k))
    (hbase : ∀ i, Function.Injective (data.base i))
    (hretained : ∀ i ∈ I, S i ⊆ data.retained)
    (houtside : ∀ i ∈ I, ∀ w ∈ S i, p ≠ data.base i w)
    (hthrough : ∀ i ∈ I, Incidence p (lines i))
    (haltered : ∀ i ∈ I, (lines i).1 ∈ data.altered i)
    (honlines : ∀ i ∈ I, ∀ w ∈ S i, Incidence (data.base i w) (lines i))
    (hsize : ∀ i, (S i).card ≤ 5) (hthin : OffPencilThin data p)
    (v : Vertex (k := k) data.altered) :
    ((selectedPositions I S).filter
      (fun x : G × Point k => v ∈ exceptionalEdge data x.1 x.2)).card ≤ 5 := by
  classical
  cases v with
  | inl ell =>
      change ((selectedPositions I S).filter
        (fun x : G × Point k => ordinaryVertex data ell ∈ exceptionalEdge data x.1 x.2)).card ≤ 5
      let E := (selectedPositions I S).filter
        (fun x : G × Point k => ordinaryVertex data ell ∈ exceptionalEdge data x.1 x.2)
      change E.card ≤ 5
      by_cases hp : Incidence p ell
      · have hempty : E = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hxS, hxhit⟩ := Finset.mem_filter.mp hx
          obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hxS
          have hjoin := joinDirection_mem_altered_of_incident_line data x.1 p x.2
            (lines x.1) (houtside x.1 hi x.2 hw) (hthrough x.1 hi)
            (honlines x.1 hi x.2 hw) (haltered x.1 hi)
          exact ordinaryVertex_notMem_exceptionalEdge_of_altered_join data p x.1 x.2
            (houtside x.1 hi x.2 hw) hjoin ell hp hxhit
        simp only [hempty, Finset.card_empty, Nat.zero_le]
      · have hone : ∀ (i : G) (w z : Point k),
            (i, w) ∈ E → (i, z) ∈ E → w = z := by
          intro i w z hw hz
          obtain ⟨hwS, hwhit⟩ := Finset.mem_filter.mp hw
          obtain ⟨hzS, hzhit⟩ := Finset.mem_filter.mp hz
          obtain ⟨hi, hwsel⟩ := mem_selectedPositions.mp hwS
          have hzsel := (mem_selectedPositions.mp hzS).2
          have hne : ell ≠ lines i := by
            intro heq
            apply hp
            rw [heq]
            exact hthrough i hi
          apply hbase i
          exact eq_of_common_incidence_of_ne_lines hne
            ((ordinaryVertex_mem_exceptionalEdge_iff data i w ell).mp hwhit).2
            (honlines i hi w hwsel)
            ((ordinaryVertex_mem_exceptionalEdge_iff data i z ell).mp hzhit).2
            (honlines i hi z hzsel)
        have hgroups : E.image Prod.fst ⊆ offPencilGroups data p ell := by
          intro i hi
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨hxS, hxhit⟩ := Finset.mem_filter.mp hx
          obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hxS
          apply (mem_offPencilGroups data p ell x.1).mpr
          refine ⟨x.2, hretained x.1 hi hw,
            ((ordinaryVertex_mem_exceptionalEdge_iff data x.1 x.2 ell).mp hxhit).2, ?_⟩
          exact joinDirection_mem_altered_of_incident_line data x.1 p x.2
            (lines x.1) (houtside x.1 hi x.2 hw) (hthrough x.1 hi)
            (honlines x.1 hi x.2 hw) (haltered x.1 hi)
        calc
          E.card = (E.image Prod.fst).card :=
            card_eq_card_image_fst_of_one_per_group E hone
          _ ≤ (offPencilGroups data p ell).card := Finset.card_le_card hgroups
          _ ≤ 5 := hthin ell hp
  | inr label =>
      rcases label with ⟨i, d, c⟩
      change ((selectedPositions I S).filter
        (fun x : G × Point k => specialVertex data i d c ∈ exceptionalEdge data x.1 x.2)).card ≤ 5
      apply card_le_five_of_subset_selectedPositions_one_group I S _ i
      · exact Finset.filter_subset _ _
      · intro x hx
        by_contra hxi
        exact specialVertex_notMem_exceptionalEdge_of_ne data i x.1 (Ne.symm hxi)
          x.2 d c (Finset.mem_filter.mp hx).2
      · exact hsize i

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
variable [DecidableEq k] [DecidableEq F] {K : ℕ}

theorem offPencilThin_of_groupPoolThin
    (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (pool : ConfigurationGroup σ → Fin K → Point F)
    (choice : ConfigurationGroup σ → Fin K)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hthin : PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv) pool)
    (p : Point F) :
    OffPencilThin
      (placedConfiguration σ (groupPlacement σ u v huv)
        (fun i => pool i (choice i)) Y X) p := by
  classical
  let data := placedConfiguration σ (groupPlacement σ u v huv)
    (fun i => pool i (choice i)) Y X
  intro ell hp
  apply (Finset.card_le_card ?_).trans (hthin p ell hp)
  intro i hi
  obtain ⟨w, hw, hinc, hdir⟩ := (mem_offPencilGroups data p ell i).mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, choice i, ?_⟩
  refine ⟨(groupPlacement σ u v huv i).apply (mapPoint σ w), ?_,
    joinDirection p (data.base i w), hdir, hinc, ?_⟩
  · exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  · exact incidence_joinLine_right p (data.base i w)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

def ordinaryLines (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered)) : Finset (AffineLine F) := C.toLeft

@[simp] theorem mem_ordinaryLines (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; k) data.altered)) (ell : AffineLine F) :
    ell ∈ ordinaryLines data C ↔ ordinaryVertex data ell ∈ C :=
  Finset.mem_toLeft

theorem ordinaryVertex_injective (data : ConfigurationData k F G) :
    Function.Injective (ordinaryVertex data) := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; by
  intro l m hlm
  exact Sum.inl.inj hlm

theorem ordinaryLines_card_le (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; k) data.altered)) :
    (ordinaryLines data C).card ≤ C.card := Finset.card_toLeft_le

variable [Fintype F]

def forcedPencilVertices (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) :
    Finset (Vertex (k := k) data.altered) :=
  (affinePencil p \ B).image (ordinaryVertex data)

theorem card_forcedPencilVertices (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (forcedPencilVertices data B p).card = (affinePencil p \ B).card :=
  Finset.card_image_of_injective _ (ordinaryVertex_injective data)

@[simp] theorem ordinaryVertex_mem_forcedPencilVertices_iff
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ forcedPencilVertices data B p ↔
      ell ∈ affinePencil p ∧ ell ∉ B := by
  constructor
  · intro h
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp h
    have hlell : l = ell := ordinaryVertex_injective data heq
    subst l
    exact Finset.mem_sdiff.mp hl
  · intro h
    exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr h)

theorem ordinaryLines_offPencil_add_onPencil_le
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered)) (p : ProjectivePoint F) :
    (ordinaryLines data C \ affinePencil p).card +
      (ordinaryLines data C ∩ affinePencil p).card ≤ C.card := by
  rw [Finset.card_sdiff_add_card_inter]
  exact ordinaryLines_card_le data C

variable [Fintype G]

theorem ordinaryLines_cover_ordinaryPoints (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) :
    ∀ x ∈ data.ordinaryPoints, ∃ ell ∈ ordinaryLines data C, Incidence x ell := by
  intro x hx
  have he : ordinaryEdge data x ∈ hypergraph data :=
    (mem_hypergraph data _).2 (Or.inl ⟨x, hx, rfl⟩)
  obtain ⟨v, hvC, hve⟩ := hC (ordinaryEdge data x) he
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hve
  exact ⟨lineThrough d x, (mem_ordinaryLines data C _).2 hvC,
    incidence_lineThrough d x⟩

theorem ordinaryVertex_mem_cover_of_pencil_survivors
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C)
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hpell : ProjectiveIncidence p (some ell))
    (hmany : 1 + (ordinaryLines data C \ affinePencil p).card <
      (data.ordinaryPoints ∩ linePoints ell).card) :
    ordinaryVertex data ell ∈ C := by
  apply (mem_ordinaryLines data C ell).1
  exact mem_cover_of_pencil_survivors data.ordinaryPoints (ordinaryLines data C)
    p ell (ordinaryLines_cover_ordinaryPoints data C hC) hpell hmany

theorem forcedPencilVertices_subset_cover
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (hmany : ∀ ell ∈ affinePencil p, ell ∉ B →
      1 + (ordinaryLines data C \ affinePencil p).card <
        (data.ordinaryPoints ∩ linePoints ell).card) :
    forcedPencilVertices data B p ⊆ C := by
  intro v hv
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hpell, hnot⟩ := Finset.mem_sdiff.mp hell
  exact ordinaryVertex_mem_cover_of_pencil_survivors data C hC p ell
    ((mem_affinePencil _ _).1 hpell) (hmany ell hpell hnot)

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

def ActiveExceptional (data : ConfigurationData k F G) (i : G)
    (v : Vertex (k := k) data.altered) : Prop :=
  ∃ w ∈ data.retained, v ∈ exceptionalEdge data i w

def LineCapable (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F)) (i : G) :
    Vertex (k := k) data.altered → Prop
  | Sum.inl ell => ell.1 ∈ axes i
  | Sum.inr tag => tag.1 = i

def lineResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Finset (Vertex (k := k) data.altered) := by
  classical
  exact C.filter fun v => LineCapable data axes i v ∧ ActiveExceptional data i v

def pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Finset (Vertex (k := k) data.altered) := by
  classical
  exact C.filter fun v => ¬ LineCapable data axes i v ∧ ActiveExceptional data i v

@[simp] theorem mem_lineResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G)
    (v : Vertex (k := k) data.altered) :
    v ∈ lineResources data axes C i ↔
      v ∈ C ∧ LineCapable data axes i v ∧ ActiveExceptional data i v := by
  classical
  simp only [lineResources, Finset.mem_filter]

@[simp] theorem mem_pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G)
    (v : Vertex (k := k) data.altered) :
    v ∈ pointResources data axes C i ↔
      v ∈ C ∧ ¬ LineCapable data axes i v ∧ ActiveExceptional data i v := by
  classical
  simp only [pointResources, Finset.mem_filter]

theorem lineResources_subset (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    lineResources data axes C i ⊆ C := by
  intro v hv
  exact ((mem_lineResources data axes C i v).1 hv).1

theorem pointResources_subset (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    pointResources data axes C i ⊆ C := by
  intro v hv
  exact ((mem_pointResources data axes C i v).1 hv).1

theorem lineResources_disjoint_pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Disjoint (lineResources data axes C i) (pointResources data axes C i) := by
  apply Finset.disjoint_left.mpr
  intro v hl hp
  exact ((mem_pointResources data axes C i v).1 hp).2.1
    ((mem_lineResources data axes C i v).1 hl).2.1

theorem lineResources_disjoint_other_of_axis_subset
    (data : ConfigurationData k F G) (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i j : G) (hij : i ≠ j)
    (haxis : axes i ⊆ data.altered j) :
    Disjoint (lineResources data axes C i)
      (lineResources data axes C j ∪ pointResources data axes C j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hline := ((mem_lineResources data axes C i v).1 hi).2.1
  have hactive : ActiveExceptional data j v := by
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ((mem_lineResources data axes C j v).1 hj).2.2
    · exact ((mem_pointResources data axes C j v).1 hj).2.2
  obtain ⟨w, _, hw⟩ := hactive
  cases v with
  | inl ell =>
      have hinc := (ordinaryVertex_mem_exceptionalEdge_iff data j w ell).1 hw
      exact hinc.1 (haxis hline)
  | inr tag =>
      rcases tag with ⟨a, d, c⟩
      have hai : a = i := hline
      subst a
      exact specialVertex_notMem_exceptionalEdge_of_ne data i j hij w d c hw

theorem forcedPencilVertices_no_action_of_altered
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (d : Direction F) (i : G) (hd : d ∈ data.altered i)
    (v : Vertex (k := k) data.altered)
    (hv : v ∈ forcedPencilVertices data B (Sum.inr d)) (w : Point k) :
    v ∉ exceptionalEdge data i w := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  have hpencil := (mem_affinePencil (Sum.inr d) ell).1
    (Finset.mem_sdiff.mp hell).1
  have hdir : d = ell.1 := hpencil
  intro hmem
  have hnot := ((ordinaryVertex_mem_exceptionalEdge_iff data i w ell).1 hmem).1
  exact hnot (hdir ▸ hd)

section CoveredEdges

variable [Fintype G]

theorem exceptional_cover_of_vertex_cover (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (i : G) :
    ∀ w ∈ data.retained, ∃ v ∈ C, v ∈ exceptionalEdge data i w := by
  intro w hw
  exact hC _ ((mem_hypergraph data _).2 (Or.inr ⟨i, w, hw, rfl⟩))

theorem exceptional_cover_sdiff_of_no_action (data : ConfigurationData k F G)
    (C P : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (i : G)
    (hP : ∀ v ∈ P, ∀ w ∈ data.retained, v ∉ exceptionalEdge data i w) :
    ∀ w ∈ data.retained, ∃ v ∈ C \ P, v ∈ exceptionalEdge data i w := by
  intro w hw
  obtain ⟨v, hvC, hve⟩ := exceptional_cover_of_vertex_cover data C hC i w hw
  refine ⟨v, Finset.mem_sdiff.mpr ⟨hvC, ?_⟩, hve⟩
  intro hvP
  exact hP v hvP w hw hve

theorem exceptional_cover_additional_of_altered
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (B : Finset (AffineLine F))
    (d : Direction F) (i : G) (hd : d ∈ data.altered i) :
    ∀ w ∈ data.retained,
      ∃ v ∈ C \ forcedPencilVertices data B (Sum.inr d),
        v ∈ exceptionalEdge data i w := by
  apply exceptional_cover_sdiff_of_no_action data C _ hC i
  intro v hv w _
  exact forcedPencilVertices_no_action_of_altered data B d i hd v hv w

end CoveredEdges

variable [Fintype k]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X
local notation "axes" => (fun i => axisDirections σ (M i))

theorem lineCapable_has_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : LineCapable cfg axes i v) :
    ∃ ell : AffineLine k, ∀ w ∈ Y,
      v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
  classical
  cases v with
  | inl ell =>
      have ha : ell.1 ∈ axisDirections σ (M i) := hv
      have hex : ∃ d : Direction k, (d = none ∨ d = some 0) ∧
          ell.1 = placedDirection σ (M i) d := by
        rcases (mem_axisDirections_iff σ (M i) ell.1).1 ha with h | h
        · exact ⟨none, Or.inl rfl, h⟩
        · exact ⟨some 0, Or.inr rfl, h⟩
      obtain ⟨d, hd, hdir⟩ := hex
      by_cases hactive : ∃ q ∈ Y, ordinaryVertex cfg ell ∈ exceptionalEdge cfg i q
      · obtain ⟨q, _, hq⟩ := hactive
        refine ⟨lineThrough d (cubeMap q), ?_⟩
        intro w _ hw
        exact cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i) hcop
          d hd ell hdir w q
          ((ordinaryVertex_mem_exceptionalEdge_iff cfg i w ell).1 hw).2
          ((ordinaryVertex_mem_exceptionalEdge_iff cfg i q ell).1 hq).2
      · refine ⟨(none, 0), ?_⟩
        intro w hw hmem
        exact (hactive ⟨w, hw, hmem⟩).elim
  | inr tag =>
      rcases tag with ⟨j, d, c⟩
      have hji : j = i := hv
      subst j
      refine ⟨(some ((cfg).inverseSlope i d), c), ?_⟩
      intro w _ hw
      exact (specialVertex_mem_exceptionalEdge_iff cfg i w d c).1 hw

theorem not_lineCapable_unique (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : ¬ LineCapable cfg axes i v)
    (p q : Point k) (hp : v ∈ exceptionalEdge cfg i p)
    (hq : v ∈ exceptionalEdge cfg i q) : cubeMap p = cubeMap q := by
  cases v with
  | inl ell =>
      have hp' := (ordinaryVertex_mem_exceptionalEdge_iff cfg i p ell).1 hp
      have hq' := (ordinaryVertex_mem_exceptionalEdge_iff cfg i q ell).1 hq
      have hout : ell.1 ∉ alteredDirections σ (M i) ∪ axisDirections σ (M i) := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hp'.1 h
        · exact hv h
      exact congrArg cubeMap
        (placedPoint_eq_of_incidence_outside_altered_axis σ (M i) (b i)
          ell hout p q hp'.2 hq'.2)
  | inr tag =>
      rcases tag with ⟨j, d, c⟩
      have hji : j ≠ i := hv
      exact (specialVertex_notMem_exceptionalEdge_of_ne cfg j i hji p d c hp).elim

theorem not_lineCapable_has_point (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : ¬ LineCapable cfg axes i v) :
    ∃ p : Point k, ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → cubeMap w = p := by
  classical
  by_cases ha : ActiveExceptional cfg i v
  · obtain ⟨q, _, hq⟩ := ha
    refine ⟨cubeMap q, ?_⟩
    intro w _ hw
    exact not_lineCapable_unique σ M b Y X i v hv w q hw hq
  · refine ⟨(0, 0), ?_⟩
    intro w hw hmem
    exact (ha ⟨w, hw, hmem⟩).elim

theorem exceptional_resource_has_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (v : Vertex (k := k) (cfg).altered) :
    ∃ ell : AffineLine k, ∀ w ∈ Y,
      v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
  classical
  by_cases hv : LineCapable cfg axes i v
  · exact lineCapable_has_line σ M b Y X hcop i v hv
  · obtain ⟨p, hp⟩ := not_lineCapable_has_point σ M b Y X i v hv
    refine ⟨lineThrough none p, ?_⟩
    intro w hw hmem
    rw [hp w hw hmem]
    exact incidence_lineThrough none p

theorem exists_line_cover_of_exceptional_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    ∃ L : Finset (AffineLine k), L.card ≤ C.card ∧
      ∀ y ∈ Y.image cubeMap, ∃ ell ∈ L, Incidence y ell := by
  classical
  let f : Vertex (k := k) (cfg).altered → AffineLine k :=
    fun v => Classical.choose (exceptional_resource_has_line σ M b Y X hcop i v)
  refine ⟨C.image f, Finset.card_image_le, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hv, hve⟩ := hcover w hw
  exact ⟨f v, Finset.mem_image_of_mem _ hv,
    Classical.choose_spec (exceptional_resource_has_line σ M b Y X hcop i v) w hw hve⟩

theorem exists_mixed_cover_of_exceptional_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    ∃ (L : Finset (AffineLine k)) (B : Finset (Point k)),
      L.card ≤ (lineResources cfg axes C i).card ∧
      B.card ≤ (pointResources cfg axes C i).card ∧
      ∀ y ∈ Y.image cubeMap, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell := by
  classical
  have hlines : ∀ v : Vertex (k := k) (cfg).altered,
      ∃ ell : AffineLine k, LineCapable cfg axes i v →
        ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
    intro v
    by_cases hv : LineCapable cfg axes i v
    · obtain ⟨ell, hell⟩ := lineCapable_has_line σ M b Y X hcop i v hv
      exact ⟨ell, fun _ => hell⟩
    · exact ⟨(none, 0), fun h => (hv h).elim⟩
  have hpoints : ∀ v : Vertex (k := k) (cfg).altered,
      ∃ p : Point k, ¬ LineCapable cfg axes i v →
        ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → cubeMap w = p := by
    intro v
    by_cases hv : LineCapable cfg axes i v
    · exact ⟨(0, 0), fun h => (h hv).elim⟩
    · obtain ⟨p, hp⟩ := not_lineCapable_has_point σ M b Y X i v hv
      exact ⟨p, fun _ => hp⟩
  let f := fun v => Classical.choose (hlines v)
  let g := fun v => Classical.choose (hpoints v)
  refine ⟨(lineResources cfg axes C i).image f,
    (pointResources cfg axes C i).image g, Finset.card_image_le,
    Finset.card_image_le, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hvC, hve⟩ := hcover w hw
  have hactive : ActiveExceptional cfg i v := ⟨w, hw, hve⟩
  by_cases hv : LineCapable cfg axes i v
  · exact Or.inr ⟨f v, Finset.mem_image_of_mem _
      ((mem_lineResources cfg axes C i v).2 ⟨hvC, hv, hactive⟩),
      Classical.choose_spec (hlines v) hv w hw hve⟩
  · apply Or.inl
    rw [Classical.choose_spec (hpoints v) hv w hw hve]
    exact Finset.mem_image_of_mem _
      ((mem_pointResources cfg axes C i v).2 ⟨hvC, hv, hactive⟩)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {V : Type*} [DecidableEq V]

theorem two_group_resource_card_le (C Ai Bi Aj Bj : Finset V)
    (hAi : Ai ⊆ C) (hBi : Bi ⊆ C) (hAj : Aj ⊆ C) (hBj : Bj ⊆ C)
    (hAiBi : Disjoint Ai Bi) (hAjBj : Disjoint Aj Bj)
    (hAiOther : Disjoint Ai (Aj ∪ Bj))
    (hAjOther : Disjoint Aj (Ai ∪ Bi)) :
    2 * Ai.card + Bi.card + 2 * Aj.card + Bj.card ≤ 2 * C.card := by
  have hAiAj : Disjoint Ai Aj := (Finset.disjoint_union_right.mp hAiOther).1
  have hAiBj : Disjoint Ai Bj := (Finset.disjoint_union_right.mp hAiOther).2
  have hAjBi : Disjoint Aj Bi := (Finset.disjoint_union_right.mp hAjOther).2
  have hlineBi : Disjoint (Ai ∪ Aj) Bi :=
    Finset.disjoint_union_left.mpr ⟨hAiBi, hAjBi⟩
  have hlineBj : Disjoint (Ai ∪ Aj) Bj :=
    Finset.disjoint_union_left.mpr ⟨hAiBj, hAjBj⟩
  have hleft : Ai.card + Aj.card + Bi.card ≤ C.card := by
    have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hAi hAj) hBi)
    rw [Finset.card_union_of_disjoint hlineBi, Finset.card_union_of_disjoint hAiAj] at h
    exact h
  have hright : Ai.card + Aj.card + Bj.card ≤ C.card := by
    have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hAi hAj) hBj)
    rw [Finset.card_union_of_disjoint hlineBj, Finset.card_union_of_disjoint hAiAj] at h
    exact h
  omega

theorem two_group_weighted_budget_impossible (s ai bi aj bj n : ℕ)
    (hs : 0 < s)
    (hi : 2 * s ≤ 2 * ai + bi) (hj : 2 * s ≤ 2 * aj + bj)
    (haccount : 2 * ai + bi + 2 * aj + bj ≤ 2 * n)
    (hbudget : n ≤ 2 * (s - 1)) : False := by
  omega

theorem two_group_resource_budget_impossible (C Ai Bi Aj Bj : Finset V)
    (s : ℕ) (hs : 0 < s)
    (hAi : Ai ⊆ C) (hBi : Bi ⊆ C) (hAj : Aj ⊆ C) (hBj : Bj ⊆ C)
    (hAiBi : Disjoint Ai Bi) (hAjBj : Disjoint Aj Bj)
    (hAiOther : Disjoint Ai (Aj ∪ Bj))
    (hAjOther : Disjoint Aj (Ai ∪ Bi))
    (hi : 2 * s ≤ 2 * Ai.card + Bi.card)
    (hj : 2 * s ≤ 2 * Aj.card + Bj.card)
    (hbudget : C.card ≤ 2 * (s - 1)) : False :=
  two_group_weighted_budget_impossible s Ai.card Bi.card Aj.card Bj.card C.card
    hs hi hj
    (two_group_resource_card_le C Ai Bi Aj Bj hAi hBi hAj hBj
      hAiBi hAjBj hAiOther hAjOther)
    hbudget

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

theorem card_forcedPencilVertices_add_card_deletedPencil
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : ProjectivePoint F) :
    (forcedPencilVertices data B p).card + (B ∩ affinePencil p).card =
      (affinePencil p).card := by
  rw [card_forcedPencilVertices]
  simpa only [Finset.inter_comm] using
    Finset.card_sdiff_add_card_inter (affinePencil p) B

theorem forced_additional_card_eq (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := let _ := instFieldk; k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) :
    (forcedPencilVertices data B p).card +
      (C \ forcedPencilVertices data B p).card = C.card := by
  simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hforced

theorem forced_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) (hC : C.card ≤ Fintype.card F) :
    (forcedPencilVertices data B p).card +
      (C \ forcedPencilVertices data B p).card ≤ Fintype.card F :=
  (forced_additional_card_eq data B p C hforced).trans_le hC

theorem pencil_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) (hC : C.card ≤ Fintype.card F) :
    (affinePencil p).card + (C \ forcedPencilVertices data B p).card ≤
      Fintype.card F + (B ∩ affinePencil p).card := by
  have hsplit := card_forcedPencilVertices_add_card_deletedPencil data B p
  have hbudget := forced_additional_card_le data B p C hforced hC
  omega

theorem finite_deletedPencil_card_pos (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : Point F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    0 < (B ∩ affinePencil (Sum.inl p)).card := by
  have hbudget := pencil_additional_card_le data B (Sum.inl p) C hforced hC
  rw [card_affinePencil_finite] at hbudget
  omega

theorem finite_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : Point F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    (C \ forcedPencilVertices data B (Sum.inl p)).card ≤
      (B ∩ affinePencil (Sum.inl p)).card - 1 := by
  have hbudget := pencil_additional_card_le data B (Sum.inl p) C hforced hC
  rw [card_affinePencil_finite] at hbudget
  omega

theorem infinite_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (d : Direction F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inr d) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    (C \ forcedPencilVertices data B (Sum.inr d)).card ≤
      (B ∩ affinePencil (Sum.inr d)).card := by
  have hbudget := pencil_additional_card_le data B (Sum.inr d) C hforced hC
  rw [card_affinePencil_infinite] at hbudget
  omega

theorem infinite_additional_card_le_of_deleted_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (d : Direction F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inr d) ⊆ C)
    (hC : C.card ≤ Fintype.card F) (N : ℕ)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ N) :
    (C \ forcedPencilVertices data B (Sum.inr d)).card ≤ N :=
  (infinite_additional_card_le data B d C hforced hC).trans hdeleted

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype k] [Fintype F]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X
local notation "axes" => (fun i => axisDirections σ (M i))

theorem exceptional_cover_card_lower_bound
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    Fintype.card k ≤ C.card := by
  obtain ⟨L, hLC, hLcover⟩ :=
    exists_line_cover_of_exceptional_cover σ M b Y X hcop i C hcover
  have hweight := hY.weighted_card_lower_bound ∅ L (by
    intro y hy
    exact Or.inr (hLcover y hy))
  simp only [Finset.card_empty, Nat.add_zero] at hweight
  omega

theorem exceptional_resource_weight_lower_bound
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    2 * Fintype.card k ≤
      2 * (lineResources cfg axes C i).card + (pointResources cfg axes C i).card := by
  obtain ⟨L, B, hL, hB, hcover'⟩ :=
    exists_mixed_cover_of_exceptional_cover σ M b Y X hcop i C hcover
  have hweight := hY.weighted_card_lower_bound B L hcover'
  omega

variable [Fintype G]

theorem single_infinite_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap))
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (d : Direction F) (i : G)
    (hd : d ∈ alteredDirections σ (M i))
    (hforced : forcedPencilVertices cfg B (Sum.inr d) ⊆ C)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ Fintype.card k - 1) :
    False := by
  have hcover := exceptional_cover_additional_of_altered cfg C hC B d i hd
  have hlower := exceptional_cover_card_lower_bound σ M b Y X hcop hY i
    (C \ forcedPencilVertices cfg B (Sum.inr d)) hcover
  have hupper := infinite_additional_card_le_of_deleted_le cfg B d C hforced hCcard
    (Fintype.card k - 1) hdeleted
  have hs : 0 < Fintype.card k := Fintype.card_pos
  omega

theorem double_infinite_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap))
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (d : Direction F) (i j : G) (hij : i ≠ j)
    (hdi : d ∈ alteredDirections σ (M i))
    (hdj : d ∈ alteredDirections σ (M j))
    (haxesij : axisDirections σ (M i) ⊆ alteredDirections σ (M j))
    (haxesji : axisDirections σ (M j) ⊆ alteredDirections σ (M i))
    (hforced : forcedPencilVertices cfg B (Sum.inr d) ⊆ C)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ 2 * (Fintype.card k - 1)) :
    False := by
  let A := C \ forcedPencilVertices cfg B (Sum.inr d)
  have hcoveri : ∀ w ∈ Y, ∃ v ∈ A, v ∈ exceptionalEdge cfg i w :=
    exceptional_cover_additional_of_altered cfg C hC B d i hdi
  have hcoverj : ∀ w ∈ Y, ∃ v ∈ A, v ∈ exceptionalEdge cfg j w :=
    exceptional_cover_additional_of_altered cfg C hC B d j hdj
  have hi := exceptional_resource_weight_lower_bound σ M b Y X hcop hY i A hcoveri
  have hj := exceptional_resource_weight_lower_bound σ M b Y X hcop hY j A hcoverj
  have hbudget : A.card ≤ 2 * (Fintype.card k - 1) :=
    infinite_additional_card_le_of_deleted_le cfg B d C hforced hCcard
      (2 * (Fintype.card k - 1)) hdeleted
  exact two_group_resource_budget_impossible A
    (lineResources cfg axes A i) (pointResources cfg axes A i)
    (lineResources cfg axes A j) (pointResources cfg axes A j)
    (Fintype.card k) Fintype.card_pos
    (lineResources_subset cfg axes A i) (pointResources_subset cfg axes A i)
    (lineResources_subset cfg axes A j) (pointResources_subset cfg axes A j)
    (lineResources_disjoint_pointResources cfg axes A i)
    (lineResources_disjoint_pointResources cfg axes A j)
    (lineResources_disjoint_other_of_axis_subset cfg axes A i j hij haxesij)
    (lineResources_disjoint_other_of_axis_subset cfg axes A j i hij.symm haxesji)
    hi hj hbudget

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype k] [Fintype F]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X

theorem forced_vertex_inside_axes
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G) (wp : Point k)
    (B : Finset (AffineLine F)) (v : Vertex (k := k) (cfg).altered)
    (hv : v ∈ forcedPencilVertices cfg B
      (Sum.inl (placedPoint σ (M i) (b i) wp)))
    (w : Point k) (hve : v ∈ exceptionalEdge cfg i w) :
    Incidence (cubeMap w) (lineThrough none (cubeMap wp)) ∨
      Incidence (cubeMap w) (lineThrough (some 0) (cubeMap wp)) := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  have hwp : Incidence (placedPoint σ (M i) (b i) wp) ell :=
    (mem_affinePencil _ ell).1 (Finset.mem_sdiff.mp hell).1
  have hw := (ordinaryVertex_mem_exceptionalEdge_iff cfg i w ell).1 hve
  by_cases haxis : ell.1 ∈ axisDirections σ (M i)
  · rcases (mem_axisDirections_iff σ (M i) ell.1).1 haxis with hd | hd
    · exact Or.inl (cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i)
        hcop none (Or.inl rfl) ell hd w wp hw.2 hwp)
    · exact Or.inr (cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i)
        hcop (some 0) (Or.inr rfl) ell hd w wp hw.2 hwp)
  · have hout : ell.1 ∉ alteredDirections σ (M i) ∪ axisDirections σ (M i) := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hw.1 h
      · exact haxis h
    have hsame : w = wp :=
      placedPoint_eq_of_incidence_outside_altered_axis σ (M i) (b i)
        ell hout w wp hw.2 hwp
    subst w
    exact Or.inl (incidence_lineThrough none (cubeMap wp))

variable [Fintype G]

theorem exists_inside_axis_line_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G) (wp : Point k)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (B : Finset (AffineLine F)) :
    ∃ L : Finset (AffineLine k),
      L.card ≤ (C \ forcedPencilVertices cfg B
        (Sum.inl (placedPoint σ (M i) (b i) wp))).card + 2 ∧
      lineThrough none (cubeMap wp) ∈ L ∧
      lineThrough (some 0) (cubeMap wp) ∈ L ∧
      ∀ y ∈ Y.image cubeMap, ∃ ell ∈ L, Incidence y ell := by
  classical
  let P := forcedPencilVertices cfg B (Sum.inl (placedPoint σ (M i) (b i) wp))
  let A := C \ P
  let f : Vertex (k := k) (cfg).altered → AffineLine k :=
    fun v => Classical.choose (exceptional_resource_has_line σ M b Y X hcop i v)
  let vertical := lineThrough none (cubeMap wp)
  let horizontal := lineThrough (some 0) (cubeMap wp)
  let L := insert vertical (insert horizontal (A.image f))
  have hvertical : vertical ∈ L := Finset.mem_insert_self _ _
  have hhorizontal : horizontal ∈ L :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcard : L.card ≤ A.card + 2 := by
    have houter := Finset.card_insert_le vertical (insert horizontal (A.image f))
    have hinner := Finset.card_insert_le horizontal (A.image f)
    have himage : (A.image f).card ≤ A.card := Finset.card_image_le
    change (insert vertical (insert horizontal (A.image f))).card ≤ A.card + 2
    omega
  refine ⟨L, hcard, hvertical, hhorizontal, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hvC, hve⟩ := exceptional_cover_of_vertex_cover cfg C hC i w hw
  by_cases hvP : v ∈ P
  · rcases forced_vertex_inside_axes σ M b Y X hcop i wp B v hvP w hve with hv | hh
    · exact ⟨vertical, hvertical, hv⟩
    · exact ⟨horizontal, hhorizontal, hh⟩
  · have hvA : v ∈ A := Finset.mem_sdiff.mpr ⟨hvC, hvP⟩
    refine ⟨f v, Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hvA)), ?_⟩
    exact Classical.choose_spec
      (exceptional_resource_has_line σ M b Y X hcop i v) w hw hve

theorem finite_inside_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G) (wp : Point k)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F))
    (hforced : forcedPencilVertices cfg B
      (Sum.inl (placedPoint σ (M i) (b i) wp)) ⊆ C)
    (hdeleted : (B ∩ affinePencil
      (Sum.inl (placedPoint σ (M i) (b i) wp))).card ≤ Fintype.card k - 1) :
    False := by
  obtain ⟨L, hLcard, hvertical, hhorizontal, hcover⟩ :=
    exists_inside_axis_line_cover σ M b Y X hcop i wp C hC B
  have hpositive := finite_deletedPencil_card_pos cfg B
    (placedPoint σ (M i) (b i) wp) C hforced hCcard
  have hremaining := finite_additional_card_le cfg B
    (placedPoint σ (M i) (b i) wp) C hforced hCcard
  have hsmall : L.card ≤ Fintype.card k := by omega
  have hdirections : (lineThrough none (cubeMap wp)).1 ≠
      (lineThrough (some 0) (cubeMap wp)).1 := by
    simp only [lineThrough_direction, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hY.not_line_cover_of_distinct_directions L hsmall
    hvertical hhorizontal hdirections hcover

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

theorem card_le_sum_capacity
    {ι V : Type*} (E : Finset ι) (C : Finset V)
    (R : V → ι → Prop) [∀ v, DecidablePred (R v)]
    (capacity : V → ℕ)
    (hcover : ∀ e ∈ E, ∃ v ∈ C, R v e)
    (hcapacity : ∀ v ∈ C, (E.filter (R v)).card ≤ capacity v) :
    E.card ≤ ∑ v ∈ C, capacity v := by
  classical
  calc
    E.card ≤ (C.biUnion fun v => E.filter (R v)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨v, hv, hve⟩ := hcover e he
      exact Finset.mem_biUnion.mpr
        ⟨v, hv, Finset.mem_filter.mpr ⟨he, hve⟩⟩
    _ ≤ ∑ v ∈ C, (E.filter (R v)).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ C, capacity v := Finset.sum_le_sum hcapacity

theorem card_le_mul_resource_card
    {ι V : Type*} (E : Finset ι) (C : Finset V)
    (R : V → ι → Prop) [∀ v, DecidablePred (R v)]
    (b : ℕ)
    (hcover : ∀ e ∈ E, ∃ v ∈ C, R v e)
    (hcapacity : ∀ v ∈ C, (E.filter (R v)).card ≤ b) :
    E.card ≤ b * C.card := by
  calc
    E.card ≤ ∑ _v ∈ C, b :=
      card_le_sum_capacity E C R (fun _ => b) hcover hcapacity
    _ = C.card * b :=
      Finset.sum_const_nat (s := C) (m := b) (f := fun _ : V => b)
        (fun _ _ => rfl)
    _ = b * C.card := Nat.mul_comm _ _

end RyserCoveringCounterexample.Construction

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {G k F : Type*} [Field k] [Field F]
variable [Fintype G] [Fintype k] [Fintype F]
variable [DecidableEq G] [DecidableEq k] [DecidableEq F]

def activeDeletionLine (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) : AffineLine F :=
  Classical.choose ((mem_activeDeletionGroups σ M b a p i.val).mp i.property)

theorem activeDeletionLine_spec (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    activeDeletionLine σ M b a p i ∈ deletedLines σ (M i.val) (b i.val) a ∧
      Incidence p (activeDeletionLine σ M b a p i) :=
  Classical.choose_spec ((mem_activeDeletionGroups σ M b a p i.val).mp i.property)

theorem activeDeletionLine_mem (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    activeDeletionLine σ M b a p i ∈ deletedLines σ (M i.val) (b i.val) a :=
  (activeDeletionLine_spec σ M b a p i).1

theorem incidence_activeDeletionLine (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    Incidence p (activeDeletionLine σ M b a p i) :=
  (activeDeletionLine_spec σ M b a p i).2

theorem activeDeletionLine_injective (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (hsep : DeletionSeparated σ M b a) :
    Function.Injective (activeDeletionLine σ M b a p) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hdisj := disjoint_deletedLines_of_separated σ M b a hsep hne
  have hmemj : activeDeletionLine σ M b a p i ∈
      deletedLines σ (M j.val) (b j.val) a := by
    rw [hij]
    exact activeDeletionLine_mem σ M b a p j
  exact (Finset.disjoint_left.mp hdisj)
    (activeDeletionLine_mem σ M b a p i) hmemj

def activeDeletionLineInPencil (σ : k →+* F) (M : G → PlaneLinearMap F)
    (b : G → Point F) (a : GadgetOutcome k) (p : Point F)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    {ell // ell ∈ deletedPencil σ M b a p} :=
  ⟨activeDeletionLine σ M b a p i,
    (mem_deletedPencil σ M b a p _).mpr
      ⟨(mem_allDeletedLines σ M b a _).mpr
        ⟨i.val, activeDeletionLine_mem σ M b a p i⟩,
        incidence_activeDeletionLine σ M b a p i⟩⟩

theorem activeDeletionLineInPencil_surjective
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    Function.Surjective (activeDeletionLineInPencil σ M b a p) := by
  intro ell
  obtain ⟨hell, hpell⟩ := (mem_deletedPencil σ M b a p ell.val).mp ell.property
  obtain ⟨i, hi⟩ := (mem_allDeletedLines σ M b a ell.val).mp hell
  have hactive : i ∈ activeDeletionGroups σ M b a p :=
    (mem_activeDeletionGroups σ M b a p i).mpr ⟨ell.val, hi, hpell⟩
  refine ⟨⟨i, hactive⟩, ?_⟩
  apply Subtype.ext
  change activeDeletionLine σ M b a p ⟨i, hactive⟩ = ell.val
  exact eq_deletedLine_of_incident_of_notMem_placedSubplane
    σ (M i) (b i) a (hout i)
    (activeDeletionLine_mem σ M b a p ⟨i, hactive⟩) hi
    (incidence_activeDeletionLine σ M b a p ⟨i, hactive⟩) hpell

theorem activeDeletionLineInPencil_bijective
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    Function.Bijective (activeDeletionLineInPencil σ M b a p) := by
  constructor
  · intro i j hij
    exact activeDeletionLine_injective σ M b a p hsep (congrArg Subtype.val hij)
  · exact activeDeletionLineInPencil_surjective σ M b a p hout

def activeDeletionGroupEquivDeletedPencil
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    {i // i ∈ activeDeletionGroups σ M b a p} ≃
      {ell // ell ∈ deletedPencil σ M b a p} :=
  Equiv.ofBijective (activeDeletionLineInPencil σ M b a p)
    (activeDeletionLineInPencil_bijective σ M b a p hsep hout)

theorem card_deletedPencil_eq_card_activeDeletionGroups
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    (deletedPencil σ M b a p).card = (activeDeletionGroups σ M b a p).card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (activeDeletionGroupEquivDeletedPencil σ M b a p hsep hout)).symm

theorem deletedPencil_eq_inter_affinePencil
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) :
    deletedPencil σ M b a p = allDeletedLines σ M b a ∩ affinePencil (Sum.inl p) := by
  ext ell
  simp only [mem_deletedPencil, Finset.mem_inter, mem_affinePencil,
    projectiveIncidence_finite_affine]

theorem card_allDeletedLines_inter_affinePencil_eq_card_activeDeletionGroups
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    (allDeletedLines σ M b a ∩ affinePencil (Sum.inl p)).card =
      (activeDeletionGroups σ M b a p).card := by
  rw [← deletedPencil_eq_inter_affinePencil σ M b a p]
  exact card_deletedPencil_eq_card_activeDeletionGroups σ M b a p hsep hout

theorem activeDeletionLine_many_placedRetainedPoints
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (ha : OriginalLineDensity a)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    5 ≤ (((retainedPoints a).image (placedPoint σ (M i.val) (b i.val))).filter
      (fun q => Incidence q (activeDeletionLine σ M b a p i))).card :=
  deletedLine_many_placedRetainedPoints σ (M i.val) (b i.val) a ha
    (activeDeletionLine_mem σ M b a p i)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype F] [Fintype G]

theorem not_isCover_of_finite_outside_lines
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : Point F) (I : Finset G) (lines : G → AffineLine F)
    (hbase : ∀ i, Function.Injective (data.base i))
    (houtside : ∀ i w, p ≠ data.base i w)
    (hthrough : ∀ i ∈ I, Incidence p (lines i))
    (haltered : ∀ i ∈ I, (lines i).1 ∈ data.altered i)
    (hdensity : ∀ i ∈ I,
      5 ≤ (data.retained.filter (fun w => Incidence (data.base i w) (lines i))).card)
    (hIcard : I.card = (B ∩ affinePencil (Sum.inl p)).card)
    (hthin : OffPencilThin data p)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hCcard : C.card ≤ Fintype.card F) :
    ¬ IsCover (hypergraph data) C := by
  classical
  intro hC
  obtain ⟨S, hS, hSout⟩ := exists_five_selection I
    (fun i => data.retained.filter (fun w => Incidence (data.base i w) (lines i)))
    hdensity
  have hretained : ∀ i ∈ I, S i ⊆ data.retained := by
    intro i hi w hw
    exact (Finset.mem_filter.mp ((hS i hi).1 hw)).1
  have honlines : ∀ i ∈ I, ∀ w ∈ S i, Incidence (data.base i w) (lines i) := by
    intro i hi w hw
    exact (Finset.mem_filter.mp ((hS i hi).1 hw)).2
  have hselectedOutside : ∀ i ∈ I, ∀ w ∈ S i, p ≠ data.base i w := by
    intro i _ w _
    exact houtside i w
  have hsize : ∀ i, (S i).card ≤ 5 := by
    intro i
    by_cases hi : i ∈ I
    · exact (hS i hi).2.le
    · rw [hSout i hi, Finset.card_empty]
      exact Nat.zero_le _
  let E := selectedPositions I S
  let R := C \ forcedPencilVertices data B (Sum.inl p)
  have hnotForced : ∀ x ∈ E, ∀ v ∈ exceptionalEdge data x.1 x.2,
      v ∉ forcedPencilVertices data B (Sum.inl p) := by
    intro x hx v hv hvforced
    obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hx
    obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hvforced
    have hpell : Incidence p ell :=
      (mem_affinePencil (Sum.inl p) ell).mp (Finset.mem_sdiff.mp hell).1
    have hjoin := joinDirection_mem_altered_of_incident_line data x.1 p x.2
      (lines x.1) (houtside x.1 x.2) (hthrough x.1 hi)
      (honlines x.1 hi x.2 hw) (haltered x.1 hi)
    exact ordinaryVertex_notMem_exceptionalEdge_of_altered_join data p x.1 x.2
      (houtside x.1 x.2) hjoin ell hpell hv
  have hcover : ∀ x ∈ E, ∃ v ∈ R, v ∈ exceptionalEdge data x.1 x.2 := by
    intro x hx
    obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hx
    have hedge : exceptionalEdge data x.1 x.2 ∈ hypergraph data :=
      (mem_hypergraph data _).mpr (Or.inr ⟨x.1, x.2, hretained x.1 hi hw, rfl⟩)
    obtain ⟨v, hvC, hv⟩ := hC _ hedge
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvC, hnotForced x hx v hv⟩, hv⟩
  have hcapacity : ∀ v ∈ R,
      (E.filter (fun x => v ∈ exceptionalEdge data x.1 x.2)).card ≤ 5 := by
    intro v _
    exact selectedPositions_hit_card_le_five data p I lines S hbase hretained
      hselectedOutside hthrough haltered honlines hsize hthin v
  have hcount : E.card ≤ 5 * R.card :=
    card_le_mul_resource_card E R
      (fun v x => v ∈ exceptionalEdge data x.1 x.2) 5 hcover hcapacity
  have hEcard : E.card = 5 * I.card :=
    card_selectedPositions I S 5 (fun i hi => (hS i hi).2)
  have hpositive : 0 < I.card := by
    rw [hIcard]
    exact finite_deletedPencil_card_pos data B p C hforced hCcard
  have hbudget : R.card ≤ I.card - 1 := by
    rw [hIcard]
    exact finite_additional_card_le data B p C hforced hCcard
  omega

variable [Fintype k]

theorem not_isCover_of_finite_outside_placedSubplanes
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (hsep : DeletionSeparated σ M b a)
    (data : ConfigurationData k F G)
    (hdataBase : ∀ i, data.base i = placedPoint σ (M i) (b i))
    (hdataAltered : ∀ i, data.altered i = alteredDirections σ (M i))
    (hdataRetained : data.retained = retainedPoints a)
    (p : Point F) (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i))
    (hthin : OffPencilThin data p)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data (allDeletedLines σ M b a) (Sum.inl p) ⊆ C)
    (hCcard : C.card ≤ Fintype.card F) :
    ¬ IsCover (hypergraph data) C := by
  classical
  let I := activeDeletionGroups σ M b a p
  let lines : G → AffineLine F := fun i =>
    if hi : i ∈ I then activeDeletionLine σ M b a p ⟨i, hi⟩ else (none, 0)
  have hline (i : G) (hi : i ∈ I) :
      lines i = activeDeletionLine σ M b a p ⟨i, hi⟩ := by
    simp only [lines, dite_eq_left hi]
  apply not_isCover_of_finite_outside_lines data (allDeletedLines σ M b a)
    p I lines
  · intro i
    rw [hdataBase i]
    exact placedPoint_injective σ (M i) (b i)
  · intro i w
    rw [hdataBase i]
    intro hpw
    exact hout i ((mem_placedSubplane_iff σ (M i) (b i) p).mpr ⟨w, hpw.symm⟩)
  · intro i hi
    rw [hline i hi]
    exact incidence_activeDeletionLine σ M b a p ⟨i, hi⟩
  · intro i hi
    rw [hline i hi, hdataAltered i]
    exact ((mem_deletedLines σ (M i) (b i) a _).mp
      (activeDeletionLine_mem σ M b a p ⟨i, hi⟩)).1
  · intro i hi
    rw [hdataRetained, hdataBase i, hline i hi]
    have hd := activeDeletionLine_many_placedRetainedPoints σ M b a p ha ⟨i, hi⟩
    rw [Finset.filter_image,
      Finset.card_image_of_injective _ (placedPoint_injective σ (M i) (b i))] at hd
    exact hd
  · exact (card_allDeletedLines_inter_affinePencil_eq_card_activeDeletionGroups
      σ M b a p hsep hout).symm
  · exact hthin
  · exact hforced
  · exact hCcard

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [Fintype F] [DecidableEq k] [DecidableEq F]

theorem card_deletedLines_through_le (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (p : Point F) :
    ((deletedLines σ M b a).filter (fun ell => Incidence p ell)).card ≤
      Fintype.card k - 1 := by
  calc
    ((deletedLines σ M b a).filter (fun ell => Incidence p ell)).card ≤
        (alteredDirections σ M).card := by
      apply Finset.card_le_card_of_injOn (fun ell : AffineLine F => ell.1)
      · intro ell hell
        exact ((mem_deletedLines σ M b a ell).mp (Finset.mem_filter.mp hell).1).1
      · intro ell hell m hm hdir
        exact line_eq_of_direction_eq_of_incidence hdir
          (Finset.mem_filter.mp hell).2 (Finset.mem_filter.mp hm).2
    _ = Fintype.card k - 1 := card_alteredDirections σ M

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem deletedPencil_eq_filter_of_mem_placedSubplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i : G) (p : Point F) (hp : p ∈ placedSubplane σ (M i) (b i)) :
    deletedPencil σ M b a p =
      (deletedLines σ (M i) (b i) a).filter (fun ell => Incidence p ell) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hglobal, hinc⟩ := (mem_deletedPencil σ M b a p ell).mp hell
    obtain ⟨j, hj⟩ := (mem_allDeletedLines σ M b a ell).mp hglobal
    by_cases hij : i = j
    · subst j
      exact Finset.mem_filter.mpr ⟨hj, hinc⟩
    · exact (not_incidence_deletedLines_of_mem_other_subplane
        σ M b a hsep hij hp hj hinc).elim
  · intro hell
    obtain ⟨hlocal, hinc⟩ := Finset.mem_filter.mp hell
    exact (mem_deletedPencil σ M b a p ell).mpr
      ⟨(mem_allDeletedLines σ M b a ell).mpr ⟨i, hlocal⟩, hinc⟩

theorem card_deletedPencil_le_of_mem_placedSubplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i : G) (p : Point F) (hp : p ∈ placedSubplane σ (M i) (b i)) :
    (deletedPencil σ M b a p).card ≤ Fintype.card k - 1 := by
  rw [deletedPencil_eq_filter_of_mem_placedSubplane σ M b a hsep i p hp]
  exact card_deletedLines_through_le σ (M i) (b i) a p

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {G k F : Type*} [Field k] [Field F]
variable [Fintype G] [Fintype k] [Fintype F]
variable [DecidableEq G] [DecidableEq k] [DecidableEq F]

theorem deletedLines_inter_affinePencil_infinite_eq_filter
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) (d : Direction F) :
    deletedLines σ M b a ∩ affinePencil (Sum.inr d) =
      (deletedLines σ M b a).filter (fun ell => ell.1 = d) := by
  ext ell
  simp only [Finset.mem_inter, Finset.mem_filter, mem_affinePencil,
    projectiveIncidence_infinite_affine]
  constructor <;> rintro ⟨hmem, hdir⟩ <;> exact ⟨hmem, hdir.symm⟩

theorem card_deletedLines_inter_affinePencil_infinite
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (d : Direction F)
    (hd : d ∈ alteredDirections σ M) :
    (deletedLines σ M b a ∩ affinePencil (Sum.inr d)).card =
      Fintype.card k - 1 := by
  rw [deletedLines_inter_affinePencil_infinite_eq_filter]
  exact card_deletedLines_of_mem_alteredDirections σ M b a ha d hd

theorem allDeletedLines_inter_affinePencil_infinite_eq_biUnion
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (d : Direction F) :
    allDeletedLines σ M b a ∩ affinePencil (Sum.inr d) =
      (Finset.univ.filter (fun i => d ∈ alteredDirections σ (M i))).biUnion
        (fun i => deletedLines σ (M i) (b i) a ∩ affinePencil (Sum.inr d)) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hglobal, hpencil⟩ := Finset.mem_inter.mp hell
    obtain ⟨i, hi⟩ := (mem_allDeletedLines σ M b a ell).mp hglobal
    have hdell : d = ell.1 := (mem_affinePencil (Sum.inr d) ell).mp hpencil
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩, Finset.mem_inter.mpr ⟨hi, hpencil⟩⟩
    rw [hdell]
    exact ((mem_deletedLines σ (M i) (b i) a ell).mp hi).1
  · intro hell
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hell
    obtain ⟨hlocal, hpencil⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_inter.mpr
      ⟨(mem_allDeletedLines σ M b a ell).mpr ⟨i, hlocal⟩, hpencil⟩

theorem card_allDeletedLines_inter_affinePencil_infinite_le
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (d : Direction F) :
    (allDeletedLines σ M b a ∩ affinePencil (Sum.inr d)).card ≤
      (Finset.univ.filter (fun i => d ∈ alteredDirections σ (M i))).card *
        (Fintype.card k - 1) := by
  rw [allDeletedLines_inter_affinePencil_infinite_eq_biUnion]
  refine Finset.card_biUnion_le.trans (le_of_eq ?_)
  exact Finset.sum_const_nat (fun i hi =>
    card_deletedLines_inter_affinePencil_infinite σ (M i) (b i) a ha d
      (Finset.mem_filter.mp hi).2)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

section Forcing

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F] [Fintype G]

theorem forcedPencilVertices_subset_of_near_pencil
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) (δ ρ : ℝ)
    (hgap : 1 + ρ * Fintype.card F < δ * Fintype.card F / 2)
    (hline : ∀ ell ∉ B,
      δ * Fintype.card F / 2 ≤ ((data.ordinaryPoints ∩ linePoints ell).card : ℝ))
    (hnear : (1 - ρ) * Fintype.card F ≤
      ((ordinaryLines data C ∩ affinePencil p).card : ℝ)) :
    forcedPencilVertices data B p ⊆ C := by
  have hbudget := (ordinaryLines_offPencil_add_onPencil_le data C p).trans hCcard
  have hbudgetReal : ((ordinaryLines data C \ affinePencil p).card : ℝ) +
      ((ordinaryLines data C ∩ affinePencil p).card : ℝ) ≤ Fintype.card F := by
    exact_mod_cast hbudget
  have hoff : ((ordinaryLines data C \ affinePencil p).card : ℝ) ≤
      ρ * Fintype.card F := by nlinarith
  apply forcedPencilVertices_subset_cover data C hC B p
  intro ell _ hell
  have hdensity := hline ell hell
  have hstrict : (1 : ℝ) + ((ordinaryLines data C \ affinePencil p).card : ℝ) <
      ((data.ordinaryPoints ∩ linePoints ell).card : ℝ) := by linarith
  exact_mod_cast hstrict

end Forcing

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]
variable (σ : k →+* F) (u v : k) (huv : u ≠ v)
variable (a : GadgetOutcome k) (b : ConfigurationGroup σ → Point F)
variable (X : Finset (Point F))

local instance : DecidableEq (ConfigurationGroup σ) := Classical.decEq _

local notation "M" => groupPlacement σ u v huv
local notation "data" => placedConfiguration σ M b (retainedPoints a) X

theorem not_isCover_actual_group_configuration
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (ha : GoodGadget a)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : 1 + (δ / 10) * Fintype.card F < δ * Fintype.card F / 2)
    (hsep : DeletionSeparated σ M b a)
    (hthin : ∀ p : Point F, OffPencilThin data p)
    (hline : ∀ ell ∉ allDeletedLines σ M b a,
      δ * Fintype.card F / 2 ≤ ((X ∩ linePoints ell).card : ℝ))
    (hnear : ∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      (∀ x ∈ X, ∃ ell ∈ L, Incidence x ell) →
      ∃ p : ProjectivePoint F,
        (1 - δ / 10) * Fintype.card F ≤ ((L ∩ affinePencil p).card : ℝ))
    (C : Finset (Vertex (k := k) (data).altered))
    (hCcard : C.card ≤ Fintype.card F) : ¬ IsCover (hypergraph data) C := by
  let _ := hδ
  classical
  intro hC
  let B := allDeletedLines σ M b a
  have hY : GadgetCoverProperty ((retainedPoints a).image cubeMap) := ha.2.2
  have hordinary := ordinaryLines_cover_ordinaryPoints data C hC
  obtain ⟨p, hp⟩ := hnear (ordinaryLines data C)
    ((ordinaryLines_card_le data C).trans hCcard) hordinary
  have hforced : forcedPencilVertices data B p ⊆ C :=
    forcedPencilVertices_subset_of_near_pencil data C hC hCcard B p δ (δ / 10)
      hgap hline hp
  cases p with
  | inr d =>
      let I : Finset (ConfigurationGroup σ) :=
        Finset.univ.filter (fun i => d ∈ groupAltered σ u v huv i)
      have hIle : I.card ≤ 2 := groupAltered_multiplicity_le_two σ u v huv d
      have hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤
          I.card * (Fintype.card k - 1) :=
        card_allDeletedLines_inter_affinePencil_infinite_le σ M b a ha.1 d
      obtain ⟨i, hi⟩ := exists_groupAltered σ u v huv hu hv d
      have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      by_cases hother : ∃ j ∈ I, j ≠ i
      · obtain ⟨j, hjI, hji⟩ := hother
        have hij : i ≠ j := hji.symm
        have hj : d ∈ groupAltered σ u v huv j := (Finset.mem_filter.mp hjI).2
        have hItwo : I.card = 2 := by
          have hgt : 1 < I.card := Finset.one_lt_card.mpr ⟨i, hiI, j, hjI, hij⟩
          omega
        rw [hItwo] at hdeleted
        exact double_infinite_center_impossible σ M b (retainedPoints a) X hcop hY
          C hC hCcard B d i j hij hi hj
          (shared_groupAltered_axes_subset σ u v huv hu hv hij hi hj)
          (shared_groupAltered_axes_subset σ u v huv hu hv hji hj hi)
          hforced hdeleted
      · have hIone : I.card = 1 := by
          have hsub : I ⊆ {i} := by
            intro j hj
            have hji : j = i := by
              by_contra hji
              exact hother ⟨j, hj, hji⟩
            exact Finset.mem_singleton.mpr hji
          have hle : I.card ≤ 1 := by
            simpa only [Finset.card_singleton] using (Finset.card_le_card hsub)
          have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hiI⟩
          omega
        rw [hIone, one_mul] at hdeleted
        exact single_infinite_center_impossible σ M b (retainedPoints a) X hcop hY
          C hC hCcard B d i hi hforced hdeleted
  | inl p =>
      by_cases hinside : ∃ i : ConfigurationGroup σ,
          p ∈ placedSubplane σ (M i) (b i)
      · obtain ⟨i, hpi⟩ := hinside
        have hdeleted := card_deletedPencil_le_of_mem_placedSubplane
          σ M b a hsep i p hpi
        have hpencil : deletedPencil σ M b a p = B ∩ affinePencil (Sum.inl p) := by
          ext ell
          simp only [mem_deletedPencil, Finset.mem_inter, mem_affinePencil,
            projectiveIncidence_finite_affine, B]
        rw [hpencil] at hdeleted
        obtain ⟨wp, rfl⟩ := (mem_placedSubplane_iff σ (M i) (b i) p).1 hpi
        exact finite_inside_center_impossible σ M b (retainedPoints a) X hcop hY
          i wp C hC hCcard B hforced hdeleted
      · have hout : ∀ i : ConfigurationGroup σ,
            p ∉ placedSubplane σ (M i) (b i) := by
          intro i hi
          exact hinside ⟨i, hi⟩
        exact not_isCover_of_finite_outside_placedSubplanes σ M b a ha.1 hsep data
          (fun _ => rfl) (fun _ => rfl) rfl p hout (hthin p) C hforced hCcard hC

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

theorem counterexampleRank_of_goodAmbientPool
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0)
    (a : GadgetOutcome k) (ha : GoodGadget a)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (K : ℕ) (pool : AmbientPool σ K)
    (hpool : GoodAmbientPool σ u v huv a ha.1 K pool)
    (hgap : 1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
      ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) :
    CounterexampleRank (Fintype.card F + 1) := by
  classical
  obtain ⟨⟨choiceFin, hchoice⟩, hrigid, hthin⟩ := hpool
  let choice : ConfigurationGroup σ → Fin K := fun i =>
    choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i)
  let b : ConfigurationGroup σ → Point F := fun i => pool i (choice i)
  let X := ambientSelectedSurvivors σ u v huv a K pool choice
  let data := ambientSelectedConfiguration σ u v huv a K pool choice
  let δ := ambientDeletionDelta (Fintype.card k) K
  have hshift : selectedShifts σ (ambientFlatPoolEquiv σ K pool) choiceFin = b := by
    funext i
    change pool ((Fintype.equivFin (ConfigurationGroup σ)).symm
      ((Fintype.equivFin (ConfigurationGroup σ)) i))
        (choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i)) =
      pool i (choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i))
    rw [Equiv.symm_apply_apply]
  have hsep : DeletionSeparated σ (groupPlacement σ u v huv) b a := by
    have h := selectedShifts_deletionSeparated σ u v huv
      (ambientFlatPoolEquiv σ K pool) choiceFin hchoice a
    rw [hshift] at h
    exact h
  obtain ⟨hline, hnear⟩ := ambientPool_goodLineCover_selected
    σ u v huv a ha.1 K pool choice δ (δ / 10) hrigid
  have hnear' : ∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      (∀ x ∈ X, ∃ ell ∈ L, Incidence x ell) →
      ∃ p : ProjectivePoint F,
        (1 - δ / 10) * Fintype.card F ≤ ((L ∩ affinePencil p).card : ℝ) := by
    intro L hL hcover
    have hsub : X ⊆ L.biUnion linePoints := by
      intro x hx
      obtain ⟨ell, hell, hxell⟩ := hcover x hx
      exact Finset.mem_biUnion.mpr ⟨ell, hell, (mem_linePoints x ell).mpr hxell⟩
    obtain ⟨p, hp⟩ := hnear L hL hsub
    refine ⟨p, ?_⟩
    have heq : LineCover.coverPencil L p = L ∩ affinePencil p := by
      ext ell
      simp only [LineCover.mem_coverPencil, Finset.mem_inter, mem_affinePencil]
    rw [heq] at hp
    exact hp
  have hthin' : ∀ p : Point F, OffPencilThin data p := fun p =>
    offPencilThin_of_groupPoolThin σ u v huv pool choice (retainedPoints a) X hthin p
  have hne : (hypergraph data).Nonempty :=
    ambientSelectedHypergraph_nonempty σ u v huv a K pool choice ha
  have hI : Intersecting (hypergraph data) :=
    ambientSelectedHypergraph_intersecting σ u v huv a K pool choice hcop hsep
  have hpart : RPartiteUniform (Fintype.card F + 1) (hypergraph data) :=
    ambientSelectedHypergraph_rPartiteUniform σ u v huv a K pool choice
  apply counterexampleRank_of_no_small_cover (Nat.zero_lt_succ _) hne hpart hI
  intro C hCcard
  have hCq : C.card ≤ Fintype.card F := by omega
  have hnot := not_isCover_actual_group_configuration σ u v huv a b X hu hv hcop ha
    δ (ambientDeletionDelta_pos _ _) hgap hsep hthin' hline hnear' C hCq
  have hdec : instDecidableEqConfigurationGroup σ =
      (inferInstance : DecidableEq (ConfigurationGroup σ)) := Subsingleton.elim _ _
  rw [hdec] at hnot
  exact hnot

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserOdd.Specification

open RyserCoveringCounterexample

def EventualOddRanks : Prop :=
  ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → p % 3 = 2 →
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → Odd n →
      CounterexampleRank (p ^ n + 1)

def InfiniteRanks : Prop :=
  Set.Infinite {r : ℕ | CounterexampleRank r}

theorem explicitFailureAt_of_counterexampleRank {r : ℕ}
    (hr : CounterexampleRank r) : Specification.ExplicitFailureAt r := by
  rcases hr with ⟨V, fin, dec, H, hpos, hne, hpart, hI, hcover, hmatch, hcard⟩
  let : Fintype V := fin
  let : DecidableEq V := dec
  refine ⟨V, fin, dec, H, hpos, hne, hpart, hpart.uniform, hI,
    hcover, hmatch, hcard, ?_⟩
  rw [hmatch, hcard, Nat.mul_one]
  exact Nat.sub_lt hpos (by decide)

end RyserOdd.Specification

namespace RyserOdd

open RyserCoveringCounterexample RyserCoveringCounterexample.Construction

theorem eventualOddRanks : Specification.EventualOddRanks := by
  classical
  obtain ⟨P, hP⟩ := exists_threshold_goodGadget
  refine ⟨P, ?_⟩
  intro p hpP hp hpmod
  obtain ⟨hp5, hgadget⟩ := hP p hpP hp hpmod
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hgadget
  have hs : 2 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  obtain ⟨u, v, hu, hv, huv⟩ := exists_distinct_nonzero (k := ZMod p) (by
    rw [ZMod.card]
    omega)
  have hcop : Nat.Coprime 3 (Fintype.card (ZMod p) - 1) :=
    coprime_three_zmod_card_sub_one hpmod
  obtain ⟨K, Q, _hK, hpool⟩ :=
    exists_goodAmbientPool_uniform.{0, 0} u v huv a ha.1 hs
  refine ⟨max 3 Q, le_max_left _ _, ?_⟩
  intro n hn hnOdd
  have hn3 : 2 < n := lt_of_lt_of_le (by decide : 2 < 3)
    ((le_max_left 3 Q).trans hn)
  have hn0 : n ≠ 0 := by omega
  have hQn : Q ≤ n := (le_max_right 3 Q).trans hn
  have hsize : Q ≤ Fintype.card (ExtensionField p n) := by
    rw [extensionField_card p n hn0]
    have hnpow : n < p ^ n := Nat.lt_pow_self hp.one_lt
    exact hQn.trans hnpow.le
  have hsub : Incidence.SmallProperSubfields (ExtensionField p n) := by
    intro S hS
    exact extensionField_properSubfield_cube_le_of_odd p n hnOdd hn3 S hS
  obtain ⟨hgap, pool, hgood⟩ :=
    hpool (ExtensionField p n) (primeEmbedding p n) hsize hsub
  have hr := counterexampleRank_of_goodAmbientPool
    (primeEmbedding p n) u v huv hu hv a ha hcop K pool hgood hgap
  simpa only [extensionField_card p n hn0] using hr

theorem infiniteRanks : Specification.InfiniteRanks := by
  obtain ⟨P, hP⟩ := eventualOddRanks
  obtain ⟨p, hpP, hp, hpmod⟩ := exists_prime_gt_mod_three_eq_two P
  obtain ⟨N, _hN, hNall⟩ := hP p hpP.le hp hpmod
  apply infinite_counterexampleRanks_of_unbounded
  intro b
  let n := 2 * (N + b) + 1
  have hn : N ≤ n := by dsimp [n]; omega
  have hbn : b < n := by dsimp [n]; omega
  have hodd : Odd n := ⟨N + b, by dsimp [n]⟩
  have hnpow : n < p ^ n := Nat.lt_pow_self hp.one_lt
  exact ⟨p ^ n + 1, (hbn.trans hnpow).trans (Nat.lt_succ_self _), hNall n hn hodd⟩

theorem eventualExplicitFailures :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → p % 3 = 2 →
      ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → Odd n →
        Specification.ExplicitFailureAt (p ^ n + 1) := by
  obtain ⟨P, hP⟩ := eventualOddRanks
  refine ⟨P, ?_⟩
  intro p hpP hp hpmod
  obtain ⟨N, hN, hall⟩ := hP p hpP hp hpmod
  exact ⟨N, hN, fun n hn hnOdd =>
    Specification.explicitFailureAt_of_counterexampleRank (hall n hn hnOdd)⟩

theorem eventualOddFailures_and_infinite_oai :
    (∃ primeThreshold : ℕ, ∀ prime : ℕ, primeThreshold ≤ prime →
      prime.Prime → prime % 3 = 2 →
      ∃ degreeThreshold : ℕ, 3 ≤ degreeThreshold ∧
        ∀ degree : ℕ, degreeThreshold ≤ degree → Odd degree →
          Specification.ExplicitFailureAt (prime ^ degree + 1)) ∧
    Set.Infinite {rank : ℕ | Specification.ExplicitFailureAt rank} := by
  refine ⟨eventualExplicitFailures, ?_⟩
  exact infiniteRanks.mono fun _rank => Specification.explicitFailureAt_of_counterexampleRank

end RyserOdd

namespace RyserOddReference

end RyserOddReference

end

end OAI
end

theorem solution :
    (∃ primeThreshold : ℕ, ∀ prime : ℕ, primeThreshold ≤ prime →
      prime.Prime → prime % 3 = 2 →
      ∃ degreeThreshold : ℕ, 3 ≤ degreeThreshold ∧
        ∀ degree : ℕ, degreeThreshold ≤ degree → Odd degree →
          OAI.RyserOdd.Specification.ExplicitFailureAt (prime ^ degree + 1)) ∧
    Set.Infinite {rank : ℕ | OAI.RyserOdd.Specification.ExplicitFailureAt rank} :=
  OAI.RyserOdd.eventualOddFailures_and_infinite_oai
