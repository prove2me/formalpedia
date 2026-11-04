-- Prove2me | solution 1 for OAI.RyserCoveringCounterexample.LineCover.uniform_linecover_probability_oddExt
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-03T23:25:41.070141+00:00
-- url     : https://prove2.me/submissions/ddfa4071-d5ec-42de-a484-8c25716a3078

import Mathlib
import Definitions.Def_RyserOddSupport
import Theorems.Thm_OAI_RyserCoveringCounterexample_Incidence_uniform_incidence_bound_oddExt

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

theorem survivors_mono_ignore {ignore larger : Finset (Finset P)}
    (h : ignore ⊆ larger) (ω : Fin n → Outcome shapes D) :
    survivors ignore ω ⊆ survivors larger ω := by
  intro x hx
  apply mem_survivors.mpr
  intro i hxi
  rcases mem_deleted.mp hxi with ⟨s, hs, hnot, hxs⟩
  exact mem_survivors.mp hx i
    (mem_deleted.mpr ⟨s, hs, fun hI => hnot (h hI), hxs⟩)

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

def FiniteCrossings {t : ℕ} (a : LineTuple F t) : Prop :=
  ∀ i j, ∃ x, Incidence x (a (Sum.inl i)) ∧ Incidence x (a (Sum.inr j))

def tupleShapes {t : ℕ} (a : LineTuple F t) : Finset (Finset (Point F)) :=
  Finset.univ.image fun i => linePoints (a i)

def AdmissibleTuple (shapes : Finset (Finset (Point F))) (D h : ℕ)
    {t : ℕ} (a : LineTuple F t) : Prop :=
  FiniteCrossings a ∧ (crossPoints a).card = t * t ∧
    ∀ S ∈ shapes, S ∉ tupleShapes a → (S ∩ crossPoints a).card ≤ 2 * D * h

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

theorem coverPencil_subset (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    coverPencil L p ⊆ L := let _ := instFintypeF; Finset.filter_subset _ _

theorem left_ne_right {t : ℕ} (a : LineTuple F t) (i j : Fin t) :
    a (Sum.inl i) ≠ a (Sum.inr j) := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; by
  intro h
  cases a.injective h

end RyserCoveringCounterexample.LineCover

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

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

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

theorem prob_ge_le_expectation_div (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expectation f / t := by
  have h := μ.prob_le_expectation (fun ω => t ≤ f ω) (fun ω => t⁻¹ * f ω)
    (fun ω => mul_nonneg (inv_nonneg.mpr ht.le) (hf ω))
    (fun ω hω => by simpa [ht.ne'] using mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr ht.le))
  rw [expectation_smul] at h
  simpa [div_eq_mul_inv, mul_comm] using h

def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

@[simp] theorem prod_weight (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (ω : Ω) (γ : Γ) :
    (μ.prod ν).weight (ω, γ) = μ.weight ω * ν.weight γ := rfl

theorem expectation_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (f : Ω × Γ → ℝ) :
    (μ.prod ν).expectation f = μ.expectation (fun ω => ν.expectation (fun γ => f (ω, γ))) := by
  simp [expectation, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

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

theorem map_uniform_of_fiber_card_eq [Nonempty Ω] [Nonempty Γ] (f : Ω → Γ)
    (hfiber : ∀ y z : Γ,
      Nat.card {x : Ω // f x = y} = Nat.card {x : Ω // f x = z}) :
    (uniform Ω).map f = uniform Γ := by
  classical
  apply eq_uniform_of_weight_eq
  intro y z
  rw [map_weight_eq_prob, map_weight_eq_prob, uniform_prob, uniform_prob]
  have hc : (Finset.univ.filter (fun x : Ω => f x = y)).card =
      (Finset.univ.filter (fun x : Ω => f x = z)).card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hfiber y z
  rw [hc]

theorem uniform_prod (Ω Γ : Type*) [Fintype Ω] [Fintype Γ]
    [Nonempty Ω] [Nonempty Γ] :
    uniform (Ω × Γ) = (uniform Ω).prod (uniform Γ) :=
  (eq_uniform_of_weight_eq ((uniform Ω).prod (uniform Γ)) (fun _ _ => rfl)).symm

theorem prob_prod_average (mu : FiniteLaw Ω) (nu : FiniteLaw Γ)
    (P : Ω × Γ → Prop) :
    (mu.prod nu).prob P = mu.expectation (fun x => nu.prob (fun y => P (x, y))) := by
  simp only [prob_eq_expectation]
  exact expectation_prod mu nu (fun z => if P z then 1 else 0)

section UniformSplit

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty Ω]

end UniformSplit

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
end

section
namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

namespace DeletionProcess

variable {δ : ℝ} (process : DeletionProcess F D δ)

def survivorSet (ω : process.Config) : Finset (Point F) := survivors ∅ ω

theorem point_survival_ge (x : Point F) :
    δ ≤ process.law.prob (fun ω => x ∈ process.survivorSet ω) := by
  change δ ≤ (FiniteLaw.pi process.trials).prob (fun ω => x ∈ survivors ∅ ω)
  rw [process.uniformSurvival]
  exact process.survivalLower

end DeletionProcess
end RyserCoveringCounterexample.LineCover

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

theorem existsUnique_projectivePoint_of_ne {l m : ProjectiveLine F}
    (hlm : l ≠ m) :
    ∃! p : ProjectivePoint F, ProjectiveIncidence p l ∧ ProjectiveIncidence p m := by
  classical
  cases l with
  | none =>
    cases m with
    | none => exact (hlm rfl).elim
    | some m =>
      refine ⟨Sum.inr m.1, ⟨trivial, rfl⟩, ?_⟩
      intro p hp
      cases p with
      | inl p => exact hp.1.elim
      | inr d => exact congrArg Sum.inr hp.2
  | some l =>
    cases m with
    | none =>
      refine ⟨Sum.inr l.1, ⟨rfl, trivial⟩, ?_⟩
      intro p hp
      cases p with
      | inl p => exact hp.2.elim
      | inr d => exact congrArg Sum.inr hp.1
    | some m =>
      by_cases hdir : l.1 = m.1
      · refine ⟨Sum.inr l.1, ⟨rfl, hdir⟩, ?_⟩
        intro p hp
        cases p with
        | inl p =>
          have heq : l = m := line_eq_of_direction_eq_of_incidence hdir hp.1 hp.2
          exact (hlm (congrArg some heq)).elim
        | inr d => exact congrArg Sum.inr hp.1
      · obtain ⟨p, hp, huniq⟩ := existsUnique_incident_of_ne_direction l m hdir
        refine ⟨Sum.inl p, hp, ?_⟩
        intro q hq
        cases q with
        | inl q => exact congrArg Sum.inl (huniq q hq)
        | inr d => exact (hdir (hq.1.symm.trans hq.2)).elim

theorem eq_projectiveLine_of_common_incidence
    {p q : ProjectivePoint F} {l m : ProjectiveLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p l) (hql : ProjectiveIncidence q l)
    (hpm : ProjectiveIncidence p m) (hqm : ProjectiveIncidence q m) : l = m := by
  obtain ⟨k, _, huniq⟩ := existsUnique_projectiveLine_of_ne hpq
  exact (huniq l ⟨hpl, hql⟩).trans (huniq m ⟨hpm, hqm⟩).symm

theorem eq_projectivePoint_of_common_incidence
    {l m : ProjectiveLine F} {p q : ProjectivePoint F}
    (hlm : l ≠ m)
    (hpl : ProjectiveIncidence p l) (hpm : ProjectiveIncidence p m)
    (hql : ProjectiveIncidence q l) (hqm : ProjectiveIncidence q m) : p = q := by
  obtain ⟨x, _, huniq⟩ := existsUnique_projectivePoint_of_ne hlm
  exact (huniq p ⟨hpl, hpm⟩).trans (huniq q ⟨hql, hqm⟩).symm

theorem existsUnique_projective_incident_of_ne_lines {l m : AffineLine F}
    (hlm : l ≠ m) :
    ∃! p : ProjectivePoint F,
      ProjectiveIncidence p (some l) ∧ ProjectiveIncidence p (some m) := by
  apply existsUnique_projectivePoint_of_ne
  intro h
  exact hlm (Option.some.inj h)

theorem eq_affineLine_of_common_projective_incidence
    {p q : ProjectivePoint F} {l m : AffineLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p (some l))
    (hql : ProjectiveIncidence q (some l))
    (hpm : ProjectiveIncidence p (some m))
    (hqm : ProjectiveIncidence q (some m)) : l = m :=
  Option.some.inj (eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm)

theorem ne_of_projectiveIncidence_of_not_projectiveIncidence
    {p q : ProjectivePoint F} {l : ProjectiveLine F}
    (hpl : ProjectiveIncidence p l) (hql : ¬ ProjectiveIncidence q l) : p ≠ q := by
  intro hpq
  exact hql (hpq ▸ hpl)

end RyserCoveringCounterexample

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

open scoped BigOperators

namespace RyserCoveringCounterexample

lemma rareAnchor_centering_raw
    {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (htotal : (∑ ω, w ω) = 1)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : (∑ ω, if E ω then w ω else 0) ≤ r) :
    let m := ∑ ω, w ω * g ω
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r := by
  classical
  let m : ℝ := ∑ ω, w ω * g ω
  change
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r

  have hconst (a : ℝ) : (∑ ω, w ω * a) = a := by
    rw [← Finset.sum_mul, htotal, one_mul]

  have hmlo : b - C ≤ m := by
    calc
      b - C = ∑ ω, w ω * (b - C) := (hconst _).symm
      _ ≤ ∑ ω, w ω * g ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hlo := (abs_le.mp (hbound ω)).1
        linarith
      _ = m := rfl

  have hmhi : m ≤ b + C := by
    calc
      m = ∑ ω, w ω * g ω := rfl
      _ ≤ ∑ ω, w ω * (b + C) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hhi := (abs_le.mp (hbound ω)).2
        linarith
      _ = b + C := hconst _

  have hmean0 : (∑ ω, w ω * (g ω - m)) = 0 := by
    calc
      (∑ ω, w ω * (g ω - m)) =
          (∑ ω, w ω * g ω) - (∑ ω, w ω * m) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ = m - m := by
        change m - (∑ ω, w ω * m) = m - m
        rw [hconst m]
      _ = 0 := sub_self m

  have hcenterBound : ∀ ω, |g ω - m| ≤ 2 * C := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor <;> linarith

  have hsqBound : ∀ ω, (g ω - b) ^ 2 ≤ C ^ 2 := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    have hminus : 0 ≤ C - (g ω - b) := by
      linarith
    have hplus : 0 ≤ C + (g ω - b) := by
      linarith
    have hprod := mul_nonneg hminus hplus
    nlinarith

  have hanchor :
      (∑ ω, w ω * (g ω - b) ^ 2) ≤ C ^ 2 * r := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) ≤
          ∑ ω, (if E ω then w ω else 0) * C ^ 2 := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hE : E ω
        · simp only [ite_eq_left hE]
          exact mul_le_mul_of_nonneg_left (hsqBound ω) (hw ω)
        · simp [hE, houtside ω hE]
      _ = (∑ ω, if E ω then w ω else 0) * C ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ r * C ^ 2 :=
        mul_le_mul_of_nonneg_right hrare (sq_nonneg C)
      _ = C ^ 2 * r := mul_comm _ _

  have hvariance :
      (∑ ω, w ω * (g ω - b) ^ 2) =
        (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) =
          ∑ ω,
            (w ω * (g ω - m) ^ 2 +
              (w ω * (g ω - m)) * (2 * (m - b)) +
              w ω * (m - b) ^ 2) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = (∑ ω, w ω * (g ω - m) ^ 2) +
            (∑ ω, w ω * (g ω - m)) * (2 * (m - b)) +
            (∑ ω, w ω) * (m - b) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul]
      _ = (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
        simp only [hmean0, htotal, zero_mul, one_mul, add_zero]

  refine ⟨hmean0, hcenterBound, ?_⟩
  have hshiftNonneg := sq_nonneg (m - b)
  linarith [hvariance, hanchor]

lemma FiniteLaw.rareAnchor_centering
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : μ.prob E ≤ r) :
    μ.expectation (fun ω => g ω - μ.expectation g) = 0 ∧
      (∀ ω, |g ω - μ.expectation g| ≤ 2 * C) ∧
      μ.expectation (fun ω => (g ω - μ.expectation g) ^ 2)
        ≤ C ^ 2 * r := by
  exact @rareAnchor_centering_raw Ω _
    μ.weight μ.nonneg μ.total g b C r E
    (fun ω => Classical.propDecidable (E ω))
    hbound houtside hrare

end RyserCoveringCounterexample

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

theorem exposureBounds_of_rareAnchor (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hM : ∀ i, 2 * C i ≤ M) :
    ExposureBounds M n mu f (fun i => (C i) ^ 2 * r i) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hhead (x : Omega) :
        |headMean mu f x - headMean mu f e| ≤ C 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hanchor 0 (Fin.cons x tail)
    have hheadoutside (x : Omega) (hx : ¬ rare 0 x) :
        headMean mu f x = headMean mu f e := by
      apply congrArg ((FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation)
      funext tail
      simpa only [update_cons_zero] using houtside 0 (Fin.cons x tail) hx
    rcases FiniteLaw.rareAnchor_centering (mu 0) (headMean mu f)
      (headMean mu f e) (C 0) (r 0) (rare 0) hhead hheadoutside (hrare 0)
      with ⟨hzero, hcenter, hsecond⟩
    refine ⟨fun x => (hcenter x).trans (hM 0), hsecond, ?_⟩
    intro x
    refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
      (fun i => C i.succ) (fun i => r i.succ) (fun i => rare i.succ)
      ?_ ?_ (fun i => hrare i.succ) (fun i => hM i.succ)
    · intro i tail
      simpa only [cons_update] using hanchor i.succ (Fin.cons x tail)
    · intro i tail hnot
      simpa only [cons_update] using houtside i.succ (Fin.cons x tail) hnot

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

theorem rare_anchor_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hCM : ∀ i, 2 * C i ≤ M)
    (hCV : (∑ i, (C i) ^ 2 * r i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (C i) ^ 2 * r i) M V u hM hV hu
    (exposureBounds_of_rareAnchor M n mu f e C r rare hanchor houtside hrare hCM)
    hCV

end RyserCoveringCounterexample.Concentration

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem tendsto_log_pow_mul_rpow_neg_atTop (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun q : ℝ => (Real.log q) ^ k * q ^ (-a)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun q : ℝ => (Real.log q) ^ k / q ^ a) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := a) (k : ℝ) ha).tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  simp only [Real.rpow_neg hq, div_eq_mul_inv]

theorem tendsto_rpow_mul_exp_neg_rpow_atTop (r : ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => q ^ r * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (r / a) c hc).comp (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hq, mul_div_cancel₀ r ha.ne']

theorem tendsto_polynomial_mul_exp_neg_rpow_atTop (p : Polynomial ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => p.eval q * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      simpa only [Polynomial.eval_add, add_mul, add_zero] using hp.add hr
  | monomial k b =>
      simpa only [Polynomial.eval_monomial, Real.rpow_natCast, mul_assoc, mul_zero] using
        (tendsto_rpow_mul_exp_neg_rpow_atTop (k : ℝ) ha hc).const_mul b

theorem tendsto_count_failure_atTop {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε) :
    Tendsto (fun q : ℝ =>
      2 * (1 + q * (q + 1)) * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)))
      atTop (𝓝 0) := by
  have hc : 0 < (16 * D ^ 5)⁻¹ := by positivity
  have ha : 0 < 2 * ε := by positivity
  have h := tendsto_polynomial_mul_exp_neg_rpow_atTop
    (2 * (1 + Polynomial.X * (Polynomial.X + 1)) : Polynomial ℝ) ha hc
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

def logarithmicSampleSize (A q : ℝ) : ℕ := ⌈A * Real.log q⌉₊

theorem tendsto_logarithmicSampleSize_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun q => Nat.le_ceil (A * Real.log q))
  exact Real.tendsto_log_atTop.const_mul_atTop hA

theorem tendsto_sampleSize_pow_mul_rpow_neg_atTop (k : ℕ) {A a : ℝ}
    (hA : 0 < A) (ha : 0 < a) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ k * q ^ (-a))
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun q : ℝ => (A + 1) ^ k * ((Real.log q) ^ k * q ^ (-a)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_log_pow_mul_rpow_neg_atTop k ha).const_mul
      ((A + 1) ^ k)
  apply squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hq _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with q hq hlog
    have harg : 0 ≤ A * Real.log q := mul_nonneg hA.le (by linarith)
    have hceil : (logarithmicSampleSize A q : ℝ) ≤ A * Real.log q + 1 :=
      (Nat.ceil_lt_add_one harg).le
    have hs : (logarithmicSampleSize A q : ℝ) ≤ (A + 1) * Real.log q := by
      nlinarith
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (logarithmicSampleSize A q)) hs k
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hq (-a))

theorem log_affine_line_count_le {q : ℝ} (hq : 4 ≤ q) :
    Real.log (q * (q + 1)) ≤ (5 / 2 : ℝ) * Real.log q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hsmall := Real.log_le_log hq1 (show q + 1 ≤ 2 * q by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq0.ne'] at hsmall
  have hlarge := Real.log_le_log
    (show 0 < (2 : ℝ) ^ 2 by norm_num) (show (2 : ℝ) ^ 2 ≤ q by nlinarith)
  rw [Real.log_pow] at hlarge
  norm_num only [Nat.cast_ofNat] at hlarge
  rw [Real.log_mul hq0.ne' hq1.ne']
  nlinarith

theorem tuple_failure_le_envelope {q A c0 : ℝ} (t : ℕ) (hq : 4 ≤ q)
    (hA : 0 < A) (ht : A * Real.log q ≤ (t : ℝ)) :
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
      2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hb : 0 < q * (q + 1) := mul_pos hq0 (by linarith)
  have hlog := log_affine_line_count_le hq
  have hcount : (q * (q + 1)) ^ (2 * t) ≤
      Real.exp (5 * (t : ℝ) * Real.log q) := by
    rw [← Real.exp_log (pow_pos hb (2 * t))]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t)]
  have hlogDiv : Real.log q ≤ (t : ℝ) / A :=
    (le_div_iff₀ hA).2 (by nlinarith [ht])
  have hexponent : 5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2 ≤
      -(c0 - 5 / A) * (t : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogDiv
      (show 0 ≤ 5 * (t : ℝ) by positivity)
    simp only [div_eq_mul_inv] at hmul ⊢
    nlinarith
  calc
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
        2 * Real.exp (5 * (t : ℝ) * Real.log q) *
          Real.exp (-c0 * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcount (by norm_num)) (Real.exp_pos _).le
    _ = 2 * Real.exp (5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2) := by
      rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg, neg_mul]
    _ ≤ 2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)

theorem tendsto_tuple_failure_atTop {A c0 : ℝ} (hc0 : 0 < c0) (hA : 5 / c0 < A) :
    Tendsto (fun q : ℝ =>
      2 * (q * (q + 1)) ^ (2 * logarithmicSampleSize A q) *
        Real.exp (-c0 * (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hA0 : 0 < A := lt_trans (div_pos (by norm_num) hc0) hA
  have hfive : 5 < A * c0 := (div_lt_iff₀ hc0).mp hA
  have hcoefficient : 0 < c0 - 5 / A := by
    have hdiv : 5 / A < c0 := (div_lt_iff₀ hA0).2 (by nlinarith)
    linarith
  have hsquare : Tendsto
      (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_logarithmicSampleSize_atTop hA0)
  have henvelope : Tendsto
      (fun q : ℝ => 2 * Real.exp (-(c0 - 5 / A) *
        (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_zero, one_mul, mul_zero] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        0 (c0 - 5 / A) hcoefficient).comp hsquare).const_mul (2 : ℝ)
  apply squeeze_zero' ?_ ?_ henvelope
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    have hq0 : 0 ≤ q := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    exact tuple_failure_le_envelope (logarithmicSampleSize A q) hq hA0
      (Nat.le_ceil (A * Real.log q))

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

def contribution (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) : Finset P := deleted ignore a ∩ test

def rare (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) : Prop := (contribution ignore test a).Nonempty

@[simp] theorem contribution_emptyOutcome (ignore : Finset (Finset P))
    (test : Finset P) : contribution ignore test (emptyOutcome shapes D) = ∅ := by
  simp [contribution]

theorem contribution_card_le (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H) :
    (contribution ignore test a).card ≤ D * H := by
  let A := a.val.filter (fun L => L.val ∉ ignore)
  change (A.biUnion Subtype.val ∩ test).card ≤ D * H
  rw [Finset.biUnion_inter]
  calc
    _ ≤ ∑ L ∈ A, (L.val ∩ test).card := Finset.card_biUnion_le
    _ ≤ ∑ _L ∈ A, H := Finset.sum_le_sum fun L hL =>
      hshape L.val L.property (Finset.mem_filter.mp hL).2
    _ = A.card * H := by simp
    _ ≤ D * H := Nat.mul_le_mul_right H
      ((Finset.card_filter_le a.val _).trans a.property)

private theorem card_sub_card_le_card_of_sdiff_subset
    {A B K : Finset P} (h : A \ B ⊆ K) :
    (A.card : ℝ) - (B.card : ℝ) ≤ (K.card : ℝ) := by
  have hc : A.card ≤ K.card + B.card :=
    (Finset.card_le_card_sdiff_add_card (s := A) (t := B)).trans
      (Nat.add_le_add_right (Finset.card_le_card h) B.card)
  have hr : (A.card : ℝ) ≤ (K.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hc
  linarith

variable [instFintypeP : Fintype P]

def retainedCount (ignore : Finset (Finset P)) (test : Finset P)
    (ω : Fin n → Outcome shapes D) : ℝ :=
  ((survivors ignore ω ∩ test).card : ℝ)

theorem survivors_update_sdiff_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore (Function.update ω i a) ∩ test) \
        (survivors ignore ω ∩ test) ⊆ contribution ignore test (ω i) := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxnew, hxold⟩
  rcases Finset.mem_inter.mp hxnew with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxi
  apply hxold
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact hxi
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem survivors_sdiff_update_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore ω ∩ test) \
        (survivors ignore (Function.update ω i a) ∩ test) ⊆
      contribution ignore test a := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxold, hxnew⟩
  rcases Finset.mem_inter.mp hxold with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxa
  apply hxnew
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hxa
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem retainedCount_update_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    -((contribution ignore test a).card : ℝ) ≤
        retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ≤
        ((contribution ignore test (ω i)).card : ℝ) := by
  have hup := card_sub_card_le_card_of_sdiff_subset
    (survivors_update_sdiff_subset ignore test ω i a)
  have hdown := card_sub_card_le_card_of_sdiff_subset
    (survivors_sdiff_update_subset ignore test ω i a)
  change -((contribution ignore test a).card : ℝ) ≤
      ((survivors ignore (Function.update ω i a) ∩ test).card : ℝ) -
        ((survivors ignore ω ∩ test).card : ℝ) ∧ _
  exact ⟨by linarith, hup⟩

theorem retainedCount_update_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    |retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω| ≤
      ((contribution ignore test (ω i)).card : ℝ) +
        ((contribution ignore test a).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_update_bounds ignore test ω i a
  have ho : 0 ≤ ((contribution ignore test (ω i)).card : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ ((contribution ignore test a).card : ℝ) := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem retainedCount_empty_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    0 ≤ retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ≤ ((contribution ignore test (ω i)).card : ℝ) := by
  simpa only [contribution_emptyOutcome, Finset.card_empty, Nat.cast_zero, neg_zero]
    using retainedCount_update_bounds ignore test ω i (emptyOutcome shapes D)

theorem retainedCount_empty_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      ((contribution ignore test (ω i)).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [abs_sub_comm, abs_of_nonneg hlo]
  exact hhi

theorem not_rare_retainedCount_eq (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (h : ¬ rare ignore test (ω i)) :
    retainedCount ignore test ω =
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) := by
  have he : contribution ignore test (ω i) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [he, Finset.card_empty, Nat.cast_zero] at hhi
  linarith

theorem retainedCount_empty_abs_le_mul (ignore : Finset (Finset P))
    (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      (D : ℝ) * (H : ℝ) := by
  apply (retainedCount_empty_abs_le ignore test ω i).trans
  exact_mod_cast contribution_card_le ignore test (ω i) H hshape

section FiniteExpectations

variable {Ω : Type*} [Fintype Ω]

theorem expectation_card_inter (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.expectation (fun ω => ((S ω ∩ test).card : ℝ)) =
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := let _ := instFintypeP; by
  have hc (ω : Ω) : ((S ω ∩ test).card : ℝ) =
      ∑ x ∈ test, if x ∈ S ω then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  simp only [FiniteLaw.expectation, hc, Finset.mul_sum,
    FiniteLaw.prob, mul_ite, mul_one, mul_zero]
  calc
    _ = ∑ x ∈ test, ∑ ω, if x ∈ S ω then μ.weight ω else (0 : ℝ) :=
      Finset.sum_comm (s := Finset.univ) (t := test)
        (f := fun (ω : Ω) (x : P) => if x ∈ S ω then μ.weight ω else (0 : ℝ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hx : x ∈ S ω <;> simp only [hx, ite_true, ite_false]

theorem prob_nonempty_inter_le (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.prob (fun ω => (S ω ∩ test).Nonempty) ≤
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := by
  rw [← expectation_card_inter μ S test]
  apply μ.prob_le_expectation
  · intro ω
    exact Nat.cast_nonneg _
  · intro ω hω
    exact Nat.one_le_cast.mpr (Finset.one_le_card.mpr hω)

end FiniteExpectations

theorem prob_rare_le (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    μ.prob (rare ignore test) ≤
      ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
  prob_nonempty_inter_le μ (deleted ignore) test

theorem expectation_retainedCount (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    (FiniteLaw.pi μ).expectation (retainedCount ignore test) =
      ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) :=
  expectation_card_inter (FiniteLaw.pi μ) (survivors ignore) test

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

theorem expectation_base_count (test : Finset (Point F)) :
    process.law.expectation (retainedCount ∅ test) =
      process.survival * (test.card : ℝ) := by
  change (FiniteLaw.pi process.trials).expectation (retainedCount ∅ test) = _
  rw [expectation_retainedCount]
  simp_rw [process.uniformSurvival]
  simp [mul_comm]

theorem expectation_totalCount :
    process.law.expectation
        (retainedCount ∅ (Finset.univ : Finset (Point F))) =
      process.survival * (Fintype.card F : ℝ) ^ 2 := by
  rw [process.expectation_base_count]
  simp only [Finset.card_univ, card_point, Nat.cast_pow]

theorem expectation_base_lineCount (l : AffineLine F) :
    process.law.expectation (retainedCount ∅ (linePoints l)) =
      process.survival * (Fintype.card F : ℝ) := by
  simpa only [card_linePoints] using process.expectation_base_count (linePoints l)

theorem prob_selected_line_le (l : AffineLine F) :
    process.law.prob (fun ω => linePoints l ∈ selected ω) ≤
      (D : ℝ) / (Fintype.card F : ℝ) := by
  change (FiniteLaw.pi process.trials).prob
      (fun ω => linePoints l ∈ selected ω) ≤ _
  calc
    _ = (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ i, ∃ S ∈ (ω i).val, S.val = linePoints l) := by
      congr 1
      funext ω
      exact propext mem_selected
    _ ≤ ∑ i, (FiniteLaw.pi process.trials).prob
        (fun ω => ∃ S ∈ (ω i).val, S.val = linePoints l) :=
      FiniteLaw.prob_exists_le (FiniteLaw.pi process.trials)
        (fun i ω => ∃ S ∈ (ω i).val, S.val = linePoints l)
    _ = ∑ i, (process.trials i).prob
        (fun a => ∃ S ∈ a.val, S.val = linePoints l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact FiniteLaw.prob_pi_coordinate process.trials i
        (fun a => ∃ S ∈ a.val, S.val = linePoints l)
    _ ≤ (D : ℝ) / (Fintype.card F : ℝ) := process.lineCap l

theorem mem_ignored_line_survivors_imp (l : AffineLine F)
    (ω : process.Config) (x : Point F)
    (hx : x ∈ survivors {linePoints l} ω) :
    x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω := by
  by_cases hselected : linePoints l ∈ selected ω
  · exact Or.inr hselected
  · left
    have heq := survivors_insert_eq_of_not_selected
      (ignore := ∅) (ω := ω) hselected
    simp only [Finset.insert_empty] at heq
    exact heq ▸ hx

theorem prob_mem_ignored_line_le (l : AffineLine F) (x : Point F) :
    process.law.prob (fun ω => x ∈ survivors {linePoints l} ω) ≤
      process.survival + (D : ℝ) / (Fintype.card F : ℝ) := by
  calc
    _ ≤ process.law.prob
        (fun ω => x ∈ survivors ∅ ω ∨ linePoints l ∈ selected ω) :=
      process.law.prob_mono
        (fun ω hx => process.mem_ignored_line_survivors_imp l ω x hx)
    _ ≤ process.law.prob (fun ω => x ∈ survivors ∅ ω) +
        process.law.prob (fun ω => linePoints l ∈ selected ω) :=
      process.law.prob_union_le _ _
    _ ≤ process.survival + (D : ℝ) / (Fintype.card F : ℝ) :=
      add_le_add (process.uniformSurvival x).le (process.prob_selected_line_le l)

theorem expectation_ignored_lineCount_bounds (l : AffineLine F) :
    process.survival * (Fintype.card F : ℝ) ≤
        process.law.expectation (retainedCount {linePoints l} (linePoints l)) ∧
      process.law.expectation (retainedCount {linePoints l} (linePoints l)) ≤
        process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
  constructor
  · rw [← process.expectation_base_lineCount l]
    apply process.law.expectation_mono
    intro ω
    change ((survivors ∅ ω ∩ linePoints l).card : ℝ) ≤
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hs, hl⟩
    exact Finset.mem_inter.mpr
      ⟨survivors_mono_ignore (Finset.empty_subset {linePoints l}) ω hs, hl⟩
  · change (FiniteLaw.pi process.trials).expectation
        (retainedCount {linePoints l} (linePoints l)) ≤ _
    rw [expectation_retainedCount]
    calc
      _ ≤ ∑ _x ∈ linePoints l,
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) :=
        Finset.sum_le_sum fun x _ => process.prob_mem_ignored_line_le l x
      _ = (Fintype.card F : ℝ) *
          (process.survival + (D : ℝ) / (Fintype.card F : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_linePoints]
      _ = process.survival * (Fintype.card F : ℝ) + (D : ℝ) := by
        have hq : (Fintype.card F : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero (α := F))
        rw [mul_add, mul_div_cancel₀ (D : ℝ) hq,
          mul_comm (Fintype.card F : ℝ) process.survival]

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem prob_rare_le_of_pointwise (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (p₀ : ℝ)
    (hpoint : ∀ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) ≤ p₀) :
    μ.prob (rare ignore test) ≤ (test.card : ℝ) * p₀ := by
  calc
    _ ≤ ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
      prob_rare_le μ ignore test
    _ ≤ ∑ _x ∈ test, p₀ := Finset.sum_le_sum fun x hx => hpoint x hx
    _ = (test.card : ℝ) * p₀ := by simp

theorem retainedCount_coordinate_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * (2 * (D : ℝ) * (H : ℝ)) ^ 2 ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.coordinate_concentration n μ (retainedCount ignore test)
    (fun _ => 2 * (D : ℝ) * (H : ℝ)) M V u hM hV hu
  · intro i ω a
    have hold : ((contribution ignore test (ω i)).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test (ω i) H hshape
    have hnew : ((contribution ignore test a).card : ℝ) ≤
        (D : ℝ) * (H : ℝ) := by
      exact_mod_cast contribution_card_le ignore test a H hshape
    apply (retainedCount_update_abs_le ignore test ω i a).trans
    linarith
  · intro i
    exact hCM
  · simpa using hCV

theorem retainedCount_rare_concentration
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V) :
    (FiniteLaw.pi μ).prob (fun ω => u ≤
        |retainedCount ignore test ω -
          (FiniteLaw.pi μ).expectation (retainedCount ignore test)|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply Concentration.rare_anchor_concentration n μ (retainedCount ignore test)
    (emptyOutcome shapes D) (fun _ => (D : ℝ) * (H : ℝ))
    (fun _ => (test.card : ℝ) * p₀) (fun _ => rare ignore test)
    M V u hM hV hu
  · intro i ω
    exact retainedCount_empty_abs_le_mul ignore test H hshape ω i
  · intro i ω h
    exact not_rare_retainedCount_eq ignore test ω i h
  · intro i
    exact prob_rare_le_of_pointwise (μ i) ignore test p₀ (hpoint i)
  · intro i
    simpa only [mul_assoc] using hCM
  · simpa [mul_assoc] using hCV

theorem prob_lt_le_prob_centered {Ω : Type*} [Fintype Ω]
    (ν : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ)
    (hmean : 2 * u ≤ ν.expectation f) :
    ν.prob (fun ω => f ω < u) ≤
      ν.prob (fun ω => u ≤ |f ω - ν.expectation f|) := by
  apply ν.prob_mono
  intro ω hω
  have hneg := neg_le_abs (f ω - ν.expectation f)
  linarith

theorem retainedCount_rare_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (p₀ : ℝ)
    (hpoint : ∀ i x, x ∈ test → (μ i).prob (fun a => x ∈ deleted ignore a) ≤ p₀)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hCM : 2 * (D : ℝ) * (H : ℝ) ≤ M)
    (hCV : (n : ℝ) * ((D : ℝ) * (H : ℝ)) ^ 2 *
      ((test.card : ℝ) * p₀) ≤ V)
    (hmean : 2 * u ≤ (FiniteLaw.pi μ).expectation (retainedCount ignore test)) :
    (FiniteLaw.pi μ).prob (fun ω => retainedCount ignore test ω < u) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
  (prob_lt_le_prob_centered (FiniteLaw.pi μ) (retainedCount ignore test) u hmean).trans
    (retainedCount_rare_concentration μ ignore test H hshape p₀ hpoint M V u
      hM hV hu hCM hCV)

theorem expectation_retainedCount_ge_of_base_survival
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (δ : ℝ)
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    δ * (test.card : ℝ) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
  rw [expectation_retainedCount]
  calc
    δ * (test.card : ℝ) = ∑ _x ∈ test, δ := by simp [mul_comm]
    _ ≤ ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (hbase x hx).trans
      apply (FiniteLaw.pi μ).prob_mono
      intro ω hω
      exact survivors_mono_ignore (Finset.empty_subset ignore) ω hω

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

private theorem fieldCard_pos_real : 0 < (Fintype.card F : ℝ) := let _ := instDecidableEqF; by
  exact_mod_cast Fintype.card_pos (α := F)

theorem total_count_concentration (hD : 0 < D) (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount ∅ Finset.univ ω -
          process.survival * (Fintype.card F : ℝ) ^ 2|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3))
          (u / (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ) =
      2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
    rw [Nat.cast_mul]
    ring
  have hV : (process.trialsCount : ℝ) *
      (2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ)) ^ 2 ≤
        4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3 := by
    rw [hC]
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  have h := retainedCount_coordinate_concentration process.trials ∅ Finset.univ
    (D * Fintype.card F)
    (fun S hS _ => by simpa using process.shapeSize S hS)
    (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ))
    (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3) u
    (by positivity) (by positivity) hu hC.le hV
  change process.law.prob (fun ω => u ≤
      |retainedCount ∅ Finset.univ ω -
        process.law.expectation (retainedCount ∅ Finset.univ)|) ≤ _ at h
  rw [process.expectation_totalCount] at h
  exact h

theorem ignored_line_count_concentration (hD : 0 < D) (l : AffineLine F)
    (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount {linePoints l} (linePoints l) ω -
          process.law.expectation (retainedCount {linePoints l} (linePoints l))|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)))
          (u / (2 * (D : ℝ) ^ 2))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * (D : ℝ) = 2 * (D : ℝ) ^ 2 := by ring
  have hV : (process.trialsCount : ℝ) * (2 * (D : ℝ) * (D : ℝ)) ^ 2 ≤
      4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) := by
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) * (D : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  exact retainedCount_coordinate_concentration process.trials {linePoints l}
    (linePoints l) D
    (fun S hS hnot => process.sparse S hS l (by simpa using hnot))
    (2 * (D : ℝ) ^ 2) (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)) u
    (by positivity) (by positivity) hu hC.le hV

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

theorem count_variance_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    (q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)) =
      q ^ (2 * ε) / (4 * D ^ 5) := by
  have hp : (q ^ (k + 1 / 2 + ε)) ^ 2 =
      q ^ (2 * ε) * q ^ (2 * k + 1) := by
    calc
      _ = q ^ ((k + 1 / 2 + ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hq.le, Real.rpow_two]
      _ = q ^ (2 * ε + (2 * k + 1)) := by congr 1; ring
      _ = _ := Real.rpow_add hq _ _
  rw [hp]
  have hpow : q ^ (2 * k + 1) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_coordinate_ratio {q D ε k : ℝ} (hq : 0 < q) (hD : D ≠ 0) :
    q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k) =
      q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  rw [show k + 1 / 2 + ε = (1 / 2 + ε) + k by ring, Real.rpow_add hq]
  have hpow : q ^ k ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  field_simp [hD, hpow]

theorem count_variance_ratio_le_coordinate {q D ε : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    q ^ (2 * ε) / (4 * D ^ 5) ≤ q ^ (1 / 2 + ε) / (2 * D ^ 2) := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hp : q ^ (2 * ε) ≤ q ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hDpow : D ^ 2 ≤ D ^ 5 := by
    calc
      D ^ 2 = D ^ 2 * 1 := by ring
      _ ≤ D ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD) (sq_nonneg D)
      _ = D ^ 5 := by ring
  have hden : 2 * D ^ 2 ≤ 4 * D ^ 5 := by nlinarith [sq_nonneg D]
  exact div_le_div₀ (Real.rpow_nonneg hq0 _) hp (by positivity) hden

theorem count_tail_le_stretched_exp {q D ε k : ℝ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (k + 1 / 2 + ε)) ^ 2 / (4 * D ^ 5 * q ^ (2 * k + 1)))
        (q ^ (k + 1 / 2 + ε) / (2 * D ^ 2 * q ^ k))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hD0 : D ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hD)
  rw [count_variance_ratio hq0 hD0, count_coordinate_ratio hq0 hD0,
    min_eq_left (count_variance_ratio_le_coordinate hq hD hε)]
  have hexponent : -(1 / 4 : ℝ) * (q ^ (2 * ε) / (4 * D ^ 5)) =
      -q ^ (2 * ε) / (16 * D ^ 5) := by
    field_simp [hD0]
    ring
  rw [hexponent]

theorem total_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (3 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q ^ 3))
        (q ^ (3 / 2 + ε) / (2 * (D : ℝ) ^ 2 * q))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [one_add_one_eq_two, mul_one, Real.rpow_one,
    show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
    show (2 : ℝ) + 1 = (3 : ℕ) by norm_num, Real.rpow_natCast] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 1) hq hDr hε)

theorem line_count_tail_le_stretched_exp {q ε : ℝ} {D : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hε : ε ≤ 1 / 2) :
    2 * Real.exp (-(1 / 4 : ℝ) *
      min ((q ^ (1 / 2 + ε)) ^ 2 / (4 * (D : ℝ) ^ 5 * q))
        (q ^ (1 / 2 + ε) / (2 * (D : ℝ) ^ 2))) ≤
      2 * Real.exp (-q ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  simpa only [mul_zero, zero_add, Real.rpow_zero, Real.rpow_one, mul_one] using
    (count_tail_le_stretched_exp (q := q) (D := (D : ℝ)) (ε := ε) (k := 0) hq hDr hε)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

def GoodCounts (process : DeletionProcess F D δ) (ε : ℝ)
    (ω : process.Config) : Prop :=
  |((survivors ∅ ω).card : ℝ) - process.survival * (Fintype.card F : ℝ) ^ 2| ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ∧
    ∀ l : AffineLine F,
      process.survival * (Fintype.card F : ℝ) -
          (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
        retainedCount {linePoints l} (linePoints l) ω ∧
      retainedCount {linePoints l} (linePoints l) ω ≤
        process.survival * (Fintype.card F : ℝ) + (D : ℝ) +
          (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε)

namespace GoodCounts

variable {process : DeletionProcess F D δ} {ε : ℝ} {ω : process.Config}

end GoodCounts

namespace DeletionProcess

variable (process : DeletionProcess F D δ)

theorem prob_not_goodCounts (ε : ℝ) (hD : 1 ≤ D)
    (_hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    process.law.prob (fun ω => ¬ GoodCounts process ε ω) ≤
      2 * (1 + (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) *
        Real.exp (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5)) := by
  have hqNat : 1 ≤ Fintype.card F :=
    Nat.succ_le_iff.mpr (Fintype.card_pos (α := F))
  have hq : 1 ≤ (Fintype.card F : ℝ) := by exact_mod_cast hqNat
  have hq0 : 0 < (Fintype.card F : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hD0 : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  let T : process.Config → Prop := fun ω =>
    (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
      |((survivors ∅ ω).card : ℝ) - process.survival * (Fintype.card F : ℝ) ^ 2|
  let L : AffineLine F → process.Config → Prop := fun l ω =>
    (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
      |retainedCount {linePoints l} (linePoints l) ω -
        process.law.expectation (retainedCount {linePoints l} (linePoints l))|
  let B : ℝ := 2 * Real.exp
    (-(Fintype.card F : ℝ) ^ (2 * ε) / (16 * (D : ℝ) ^ 5))
  have htotal : process.law.prob T ≤ B := by
    have h := (process.total_count_concentration hD0
      ((Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (total_count_tail_le_stretched_exp hq hD hεhalf)
    simpa only [T, B, retainedCount, Finset.inter_univ] using h
  have hline (l : AffineLine F) : process.law.prob (L l) ≤ B := by
    exact (process.ignored_line_count_concentration hD0 l
      ((Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε))
      (Real.rpow_pos_of_pos hq0 _)).trans
        (line_count_tail_le_stretched_exp hq hD hεhalf)
  have hcover : ∀ ω, ¬ GoodCounts process ε ω → T ω ∨ ∃ l, L l ω := by
    intro ω hbad
    by_cases ht : T ω
    · exact Or.inl ht
    · right
      by_contra hlines
      apply hbad
      refine ⟨?_, ?_⟩
      · exact (lt_of_not_ge ht).le
      · intro l
        have hl : ¬ L l ω := fun h => hlines ⟨l, h⟩
        have habs :
            |retainedCount {linePoints l} (linePoints l) ω -
              process.law.expectation (retainedCount {linePoints l} (linePoints l))| ≤
            (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 + ε) := (lt_of_not_ge hl).le
        obtain ⟨hlo, hhi⟩ := abs_le.mp habs
        obtain ⟨hmlo, hmhi⟩ := process.expectation_ignored_lineCount_bounds l
        constructor <;> linarith
  calc
    _ ≤ process.law.prob (fun ω => T ω ∨ ∃ l, L l ω) :=
      process.law.prob_mono hcover
    _ ≤ process.law.prob T + process.law.prob (fun ω => ∃ l, L l ω) :=
      process.law.prob_union_le T (fun ω => ∃ l, L l ω)
    _ ≤ B + ∑ l, process.law.prob (L l) :=
      add_le_add htotal (FiniteLaw.prob_exists_le process.law L)
    _ ≤ B + ∑ _l : AffineLine F, B :=
      add_le_add le_rfl (Finset.sum_le_sum fun l _ => hline l)
    _ = (1 + (Fintype.card (AffineLine F) : ℝ)) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = _ := by
      simp only [card_affineLine, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      dsimp only [B]
      ring

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {P Λ : Type*} [instDecidableEqP : DecidableEq P] [instDecidableEqΛ : DecidableEq Λ]

def multiplicity (I : P → Λ → Prop) (L : Finset Λ) (x : P) : ℕ :=
  (L.filter (I x)).card

def coveredPoints (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : Finset P :=
  X.filter fun x => 0 < multiplicity I L x

def overlapExcess (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : ℕ :=
  ∑ x ∈ X, (multiplicity I L x - 1)

def orderedPairMass (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) : ℕ :=
  ∑ x ∈ X, multiplicity I L x * (multiplicity I L x - 1)

def heavyPoints (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T : ℝ) :
    Finset P := X.filter fun x => T ≤ (multiplicity I L x : ℝ)

theorem incidence_double_count (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ l ∈ L, (X.filter fun x => I x l).card) =
      ∑ x ∈ X, multiplicity I L x := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  simp only [multiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_multiplicity_eq_covered_add_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ x ∈ X, multiplicity I L x) =
      (coveredPoints I X L).card + overlapExcess I X L := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  calc
    _ = ∑ x ∈ X, ((if 0 < multiplicity I L x then 1 else 0) +
        (multiplicity I L x - 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      cases h : multiplicity I L x with
      | zero => simp
      | succ n => simp [Nat.add_comm]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]
      rfl

theorem incidence_eq_covered_add_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (∑ l ∈ L, (X.filter fun x => I x l).card) =
      (coveredPoints I X L).card + overlapExcess I X L := by
  rw [incidence_double_count, sum_multiplicity_eq_covered_add_excess]

theorem covered_add_uncovered_card
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) :
    (coveredPoints I X L).card + (X \ coveredPoints I X L).card = X.card := let _ := instDecidableEqΛ; by
  rw [Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)

theorem cover_count_bounds
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ)
    (d q e0 e1 b δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ d) (hq : 0 < q) (he1 : 0 ≤ e1)
    (hsize : d * q ^ 2 - e0 ≤ (X.card : ℝ))
    (hline : ∀ l ∈ L, ((X.filter fun x => I x l).card : ℝ) ≤ d * q + e1)
    (huncovered : ((X \ coveredPoints I X L).card : ℝ) ≤ b)
    (hcard : (L.card : ℝ) ≤ q) :
    (overlapExcess I X L : ℝ) ≤ e0 + q * e1 + b ∧
      q - (L.card : ℝ) ≤ (e0 + q * e1 + b) / (δ * q) := by
  let N : ℝ := X.card
  let M : ℝ := L.card
  let C : ℝ := (coveredPoints I X L).card
  let U : ℝ := (X \ coveredPoints I X L).card
  let E : ℝ := overlapExcess I X L
  let J : ℝ := ∑ l ∈ L, ((X.filter fun x => I x l).card : ℝ)
  have hcount : J = C + E := by
    dsimp [J, C, E]
    exact_mod_cast incidence_eq_covered_add_excess I X L
  have hpartition : C + U = N := by
    dsimp [C, U, N]
    exact_mod_cast covered_add_uncovered_card I X L
  have hupper : J ≤ M * (d * q + e1) := by
    calc
      J ≤ ∑ _l ∈ L, (d * q + e1) := Finset.sum_le_sum hline
      _ = _ := by simp [M, mul_add]
  have hcap : 0 ≤ d * q + e1 :=
    add_nonneg (mul_nonneg (hδ.le.trans hd) hq.le) he1
  have hupperQ := hupper.trans (mul_le_mul_of_nonneg_right hcard hcap)
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hmerr : M * e1 ≤ q * e1 := mul_le_mul_of_nonneg_right hcard he1
  have hN : d * q ^ 2 - e0 ≤ N := hsize
  have hU : U ≤ b := huncovered
  have hM : M ≤ q := hcard
  have hEbound : E ≤ e0 + q * e1 + b := by
    nlinarith [hupperQ, hcount, hpartition, hN, hU]
  have hgap : d * q * (q - M) ≤ e0 + q * e1 + b := by
    nlinarith [hupper, hcount, hpartition, hN, hU, hE0, hmerr]
  have hscale : δ * q * (q - M) ≤ d * q * (q - M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hq.le)
      (sub_nonneg.mpr hM)
  refine ⟨hEbound, ?_⟩
  apply (le_div_iff₀ (mul_pos hδ hq)).2
  simpa only [mul_comm] using hscale.trans hgap

theorem heavyPoints_card_mul_le_excess
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T : ℝ) (hT : 1 < T) :
    ((heavyPoints I X L T).card : ℝ) * (T - 1) ≤ (overlapExcess I X L : ℝ) := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  have hsum : (∑ x ∈ X, ((multiplicity I L x - 1 : ℕ) : ℝ)) =
      (overlapExcess I X L : ℝ) := by simp only [overlapExcess, Nat.cast_sum]
  rw [← hsum]
  calc
    _ = ∑ _x ∈ heavyPoints I X L T, (T - 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ heavyPoints I X L T, ((multiplicity I L x - 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxT : T ≤ (multiplicity I L x : ℝ) := (Finset.mem_filter.mp hx).2
      have hnR : (1 : ℝ) ≤ multiplicity I L x := hT.le.trans hxT
      have hn : 1 ≤ multiplicity I L x := by exact_mod_cast hnR
      rw [Nat.cast_sub hn, Nat.cast_one]
      exact sub_le_sub_right hxT 1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro x hx hxnot; exact Nat.cast_nonneg _)

theorem orderedPairMass_le_light_add_heavy
    (I : P → Λ → Prop) (X : Finset P) (L : Finset Λ) (T R : ℝ)
    (hT : 0 ≤ T) (hR : ∀ x ∈ X, (multiplicity I L x : ℝ) ≤ R) :
    (orderedPairMass I X L : ℝ) ≤ T * (overlapExcess I X L : ℝ) +
      R * ∑ x ∈ heavyPoints I X L T, (multiplicity I L x : ℝ) := let _ := instDecidableEqP; let _ := instDecidableEqΛ; by
  have hpoint (x : P) (hx : x ∈ X) :
      (multiplicity I L x : ℝ) * ((multiplicity I L x - 1 : ℕ) : ℝ) ≤
        T * ((multiplicity I L x - 1 : ℕ) : ℝ) +
          if T ≤ (multiplicity I L x : ℝ) then R * (multiplicity I L x : ℝ) else 0 := by
    have ha0 : 0 ≤ ((multiplicity I L x - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn0 : 0 ≤ (multiplicity I L x : ℝ) := Nat.cast_nonneg _
    have haN : ((multiplicity I L x - 1 : ℕ) : ℝ) ≤ (multiplicity I L x : ℝ) := by
      exact_mod_cast Nat.sub_le (multiplicity I L x) 1
    by_cases hh : T ≤ (multiplicity I L x : ℝ)
    · simp only [ite_eq_left hh]
      have hp := mul_le_mul_of_nonneg_left (haN.trans (hR x hx)) hn0
      nlinarith [mul_nonneg hT ha0]
    · simpa only [ite_eq_right hh, add_zero] using
        mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hh)) ha0
  have hsum := Finset.sum_le_sum hpoint
  simpa only [orderedPairMass, overlapExcess, heavyPoints, Nat.cast_sum,
    Nat.cast_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter,
    mul_ite, mul_zero] using hsum

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

def cleanLines (ω : Fin n → Outcome shapes D) (L : Finset (AffineLine F)) :
    Finset (AffineLine F) := L.filter fun l => linePoints l ∉ selected ω

theorem cleanLines_subset (ω : Fin n → Outcome shapes D) (L : Finset (AffineLine F)) :
    cleanLines ω L ⊆ L := Finset.filter_subset _ _

theorem cleanLines_not_selected {ω : Fin n → Outcome shapes D}
    {L : Finset (AffineLine F)} {l : AffineLine F} (hl : l ∈ cleanLines ω L) :
    linePoints l ∉ selected ω := (Finset.mem_filter.mp hl).2

theorem survivor_incidence_not_selected {ω : Fin n → Outcome shapes D}
    {x : Point F} {l : AffineLine F} (hx : x ∈ survivors ∅ ω)
    (hl : Incidence x l) : linePoints l ∉ selected ω := by
  intro hs
  have hactive : linePoints l ∈ selected ω \ ∅ := by simpa using hs
  exact mem_survivors_active.mp hx (linePoints l) hactive ((mem_linePoints x l).mpr hl)

theorem survivors_inter_cleanLines (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) :
    survivors ∅ ω ∩ L.biUnion linePoints =
      survivors ∅ ω ∩ (cleanLines ω L).biUnion linePoints := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_inter.mp hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_inter.mpr ⟨hs, Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_filter.mpr ⟨hl, survivor_incidence_not_selected hs
        ((mem_linePoints x l).mp hxl)⟩, hxl⟩⟩
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_inter.mp hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_inter.mpr ⟨hs,
      Finset.mem_biUnion.mpr ⟨l, cleanLines_subset ω L hl, hxl⟩⟩

theorem survivors_sdiff_cleanLines (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) :
    survivors ∅ ω \ L.biUnion linePoints =
      survivors ∅ ω \ (cleanLines ω L).biUnion linePoints := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro hclean
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hclean
    exact hc (Finset.mem_biUnion.mpr ⟨l, cleanLines_subset ω L hl, hxl⟩)
  · intro hx
    obtain ⟨hs, hc⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro horig
    have hboth := Finset.mem_inter.mpr ⟨hs, horig⟩
    rw [survivors_inter_cleanLines] at hboth
    exact hc (Finset.mem_inter.mp hboth).2

theorem coverPencil_mono {L K : Finset (AffineLine F)} (h : L ⊆ K)
    (p : ProjectivePoint F) : coverPencil L p ⊆ coverPencil K p := by
  intro l hl
  obtain ⟨hL, hi⟩ := (mem_coverPencil L p l).mp hl
  exact (mem_coverPencil K p l).mpr ⟨h hL, hi⟩

theorem coveredPoints_eq_inter_biUnion (X : Finset (Point F))
    (L : Finset (AffineLine F)) :
    coveredPoints Incidence X L = X ∩ L.biUnion linePoints := by
  ext x
  change x ∈ X.filter (fun x => 0 < multiplicity Incidence L x) ↔ _
  rw [Finset.mem_filter, Finset.mem_inter]
  unfold multiplicity
  have hfilter :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hn
    obtain ⟨hL, hi⟩ := Finset.mem_filter.mp hl
    exact ⟨hx, Finset.mem_biUnion.mpr ⟨l, hL, (mem_linePoints x l).mpr hi⟩⟩
  · rintro ⟨hx, hl⟩
    obtain ⟨l, hL, hi⟩ := Finset.mem_biUnion.mp hl
    exact ⟨hx, Finset.card_pos.mpr ⟨l,
      Finset.mem_filter.mpr ⟨hL, (mem_linePoints x l).mp hi⟩⟩⟩

theorem survivors_ignore_tuple_eq {t : ℕ} (ω : Fin n → Outcome shapes D)
    (a : LineTuple F t) (ha : ∀ i, linePoints (a i) ∉ selected ω) :
    survivors (tupleShapes a) ω = survivors ∅ ω := by
  have hd : selected ω \ tupleShapes a = selected ω := by
    ext S
    simp only [Finset.mem_sdiff]
    constructor
    · exact And.left
    · intro hs
      refine ⟨hs, ?_⟩
      intro ht
      obtain ⟨i, rfl⟩ := (mem_tupleShapes a S).mp ht
      exact ha i hs
  ext x
  rw [mem_survivors_active, mem_survivors_active, hd, Finset.sdiff_empty]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

def countTailConstant (D H : ℕ) (δ : ℝ) : ℝ :=
  min (δ ^ 2 / (16 * (D : ℝ) ^ 2 * ((D : ℝ) * (H : ℝ)) ^ 2))
    (δ / (16 * ((D : ℝ) * (H : ℝ))))

def tupleTailConstant (D h : ℕ) (δ : ℝ) : ℝ :=
  countTailConstant D (2 * D * h) δ

theorem countTailConstant_pos {D H : ℕ} {δ : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hδ : 0 < δ) :
    0 < countTailConstant D H δ := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  unfold countTailConstant
  apply lt_min <;> positivity

theorem tupleTailConstant_pos {D h : ℕ} {δ : ℝ}
    (hD : 0 < D) (hh : 0 < h) (hδ : 0 < δ) :
    0 < tupleTailConstant D h δ :=
  countTailConstant_pos hD
    (Nat.mul_pos (Nat.mul_pos (by decide) hD) hh) hδ

private theorem variance_budget_real (n D q C t : ℝ)
    (hD : 0 ≤ D) (hq : 0 < q) (hn : n ≤ D * q) :
    n * C ^ 2 * (t ^ 2 * (D / q)) ≤ D ^ 2 * C ^ 2 * t ^ 2 := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hscale : 0 ≤ C ^ 2 * (t ^ 2 * (D / q)) :=
    mul_nonneg (sq_nonneg C)
      (mul_nonneg (sq_nonneg t) (div_nonneg hD (le_of_lt hq)))
  calc
    n * C ^ 2 * (t ^ 2 * (D / q)) =
        n * (C ^ 2 * (t ^ 2 * (D / q))) := by ring
    _ ≤ (D * q) * (C ^ 2 * (t ^ 2 * (D / q))) :=
      mul_le_mul_of_nonneg_right hn hscale
    _ = D ^ 2 * C ^ 2 * t ^ 2 := by
      field_simp [hq0]

private theorem tail_exponent_identity (D C T δ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hT : 0 < T) :
    -(1 / 4 : ℝ) *
        min (((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2))
          ((δ * T ^ 2 / 2) / (2 * C)) =
      -(min (δ ^ 2 / (16 * D ^ 2 * C ^ 2))
          (δ / (16 * C))) * T ^ 2 := by
  let a : ℝ := δ ^ 2 / (16 * D ^ 2 * C ^ 2)
  let b : ℝ := δ / (16 * C)
  have hA :
      ((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2) =
        4 * a * T ^ 2 := by
    dsimp [a]
    field_simp [ne_of_gt hD, ne_of_gt hC, ne_of_gt hT]; ring
  have hB : (δ * T ^ 2 / 2) / (2 * C) = 4 * b * T ^ 2 := by
    dsimp [b]
    field_simp [ne_of_gt hC]; ring
  change -(1 / 4 : ℝ) * min _ _ = -(min a b) * T ^ 2
  rw [hA, hB]
  rcases le_total a b with h | h
  · have hs : 4 * a * T ^ 2 ≤ 4 * b * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_left hs, min_eq_left h]
    ring
  · have hs : 4 * b * T ^ 2 ≤ 4 * a * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_right hs, min_eq_right h]
    ring

section General

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem retainedCount_square_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H q t : ℕ) (δ : ℝ)
    (hD : 0 < D) (hH : 0 < H) (hq : 0 < q) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * q) (hcard : test.card = t * t)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (hpoint : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ∅ a) ≤ (D : ℝ) / (q : ℝ))
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob
        (fun ω => retainedCount ignore test ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(countTailConstant D H δ) * (t : ℝ) ^ 2) := by
  let C : ℝ := (D : ℝ) * (H : ℝ)
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have htr : 0 < (t : ℝ) := by exact_mod_cast ht
  have hC : 0 < C := mul_pos hDr hHr
  have hnr : (n : ℝ) ≤ (D : ℝ) * (q : ℝ) := by exact_mod_cast hn
  have hcardReal : (test.card : ℝ) = (t : ℝ) ^ 2 := by
    rw [hcard, Nat.cast_mul, pow_two]
  have hpointIgnore : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ignore a) ≤ (D : ℝ) / (q : ℝ) := by
    intro i x hx
    calc
      _ ≤ (μ i).prob (fun a => x ∈ deleted ∅ a) := by
        apply (μ i).prob_mono
        intro a hxa
        rcases mem_deleted.mp hxa with ⟨L, hL, hnot, hxL⟩
        exact mem_deleted.mpr ⟨L, hL, by simp, hxL⟩
      _ ≤ _ := hpoint i x hx
  have hCV : (n : ℝ) * C ^ 2 * ((test.card : ℝ) * ((D : ℝ) / (q : ℝ))) ≤
      (D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2 := by
    rw [hcardReal]
    exact variance_budget_real (n : ℝ) (D : ℝ) (q : ℝ) C (t : ℝ)
      hDr.le hqr hnr
  have hmean0 := expectation_retainedCount_ge_of_base_survival μ ignore test δ hbase
  rw [hcardReal] at hmean0
  have hmean : 2 * (δ * (t : ℝ) ^ 2 / 2) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
    calc
      _ = δ * (t : ℝ) ^ 2 := by ring
      _ ≤ _ := hmean0
  have htail := retainedCount_rare_lower_tail μ ignore test H hshape
    ((D : ℝ) / (q : ℝ)) hpointIgnore
    (2 * C) ((D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2)
    (δ * (t : ℝ) ^ 2 / 2)
    (by positivity) (by positivity) (by positivity)
    (le_of_eq (by dsimp [C]; ring)) hCV hmean
  apply htail.trans_eq
  apply congrArg (fun z : ℝ => 2 * Real.exp z)
  simpa only [countTailConstant, C] using
    tail_exponent_identity (D : ℝ) C (t : ℝ) δ hDr hC htr

end General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n h t : ℕ}

theorem admissibleTuple_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (a : LineTuple F t) (ha : AdmissibleTuple shapes D h a)
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω =>
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hH : 0 < 2 * D * h := Nat.mul_pos (Nat.mul_pos (by decide) hD) hh
  have hq : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  simpa only [tupleTailConstant] using retainedCount_square_lower_tail
    μ (tupleShapes a) (crossPoints a) (2 * D * h) (Fintype.card F) t δ
    hD hH hq ht hδ hn ha.2.1 ha.2.2
    (fun i x _ => hpoint i x) (fun x _ => hbase x)

theorem prob_exists_admissibleTuple_bad_le
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * (Fintype.card (LineTuple F t) : ℝ) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  classical
  calc
    _ ≤ ∑ a : LineTuple F t, (FiniteLaw.pi μ).prob (fun ω =>
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) :=
      (FiniteLaw.pi μ).prob_exists_le _
    _ ≤ ∑ _a : LineTuple F t,
        2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : AdmissibleTuple shapes D h a
      · calc
          _ ≤ (FiniteLaw.pi μ).prob (fun ω =>
              retainedCount (tupleShapes a) (crossPoints a) ω <
                δ * (t : ℝ) ^ 2 / 2) := by
            apply (FiniteLaw.pi μ).prob_mono
            intro ω hω
            exact hω.2
          _ ≤ _ := admissibleTuple_lower_tail μ a ha δ hD hh ht hδ hn hpoint hbase
      · simp only [ha, false_and, FiniteLaw.prob_false]
        positivity
    _ = _ := by simp [mul_assoc, mul_comm]

theorem card_lineTuple_le (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (t : ℕ) :
    Fintype.card (LineTuple F t) ≤
      (Fintype.card F * (Fintype.card F + 1)) ^ (2 * t) := by
  classical
  calc
    Fintype.card (LineTuple F t) ≤
        Fintype.card ((Fin t ⊕ Fin t) → AffineLine F) :=
      Fintype.card_le_of_injective
        (fun a : LineTuple F t =>
          (a : (Fin t ⊕ Fin t) → AffineLine F))
        Function.Embedding.coe_injective
    _ = _ := by
      rw [Fintype.card_fun]
      simp [AffineLine, Direction, two_mul, Nat.mul_comm]

theorem prob_exists_admissibleTuple_bad_le_card_bound
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hcard : (Fintype.card (LineTuple F t) : ℝ) ≤
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) := by
    exact_mod_cast card_lineTuple_le F t
  apply (prob_exists_admissibleTuple_bad_le μ δ hD hh ht hδ hn hpoint hbase).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_pos _).le

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ : ℝ}

def GoodTuples (process : DeletionProcess F D δ) (h t : ℕ)
    (ω : process.Config) : Prop :=
  ∀ a : LineTuple F t, AdmissibleTuple process.shapes D h a →
    δ * (t : ℝ) ^ 2 / 2 ≤ retainedCount (tupleShapes a) (crossPoints a) ω

theorem not_goodTuples_iff (process : DeletionProcess F D δ) (h t : ℕ)
    (ω : process.Config) :
    ¬ GoodTuples process h t ω ↔
      ∃ a : LineTuple F t, AdmissibleTuple process.shapes D h a ∧
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2 := by
  classical
  simp only [GoodTuples, not_forall, not_le, exists_prop]

theorem DeletionProcess.prob_not_goodTuples (process : DeletionProcess F D δ)
    (h t : ℕ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ) :
    process.law.prob (fun ω => ¬ GoodTuples process h t ω) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  calc
    _ ≤ process.law.prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple process.shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) := by
      apply process.law.prob_mono
      intro ω hω
      exact (not_goodTuples_iff process h t ω).mp hω
    _ ≤ _ := prob_exists_admissibleTuple_bad_le_card_bound process.trials δ
      hD hh ht hδ process.trialsCount_le process.pointCap
      (fun x => process.point_survival_ge x)

namespace GoodTuples

variable {process : DeletionProcess F D δ} {h t : ℕ} {ω : process.Config}

theorem clean_crosscard_ge (hgood : GoodTuples process h t ω)
    (L : Finset (AffineLine F)) (a : LineTuple F t)
    (ha : AdmissibleTuple process.shapes D h a)
    (hclean : ∀ i, a i ∈ cleanLines ω L) :
    δ * (t : ℝ) ^ 2 / 2 ≤
      ((process.survivorSet ω ∩ crossPoints a).card : ℝ) := by
  have heq := survivors_ignore_tuple_eq ω a
    (fun i => cleanLines_not_selected (hclean i))
  have hbound := hgood a ha
  change δ * (t : ℝ) ^ 2 / 2 ≤
    ((survivors (tupleShapes a) ω ∩ crossPoints a).card : ℝ) at hbound
  change δ * (t : ℝ) ^ 2 / 2 ≤
    ((survivors ∅ ω ∩ crossPoints a).card : ℝ)
  rw [heq] at hbound
  exact hbound

theorem no_sparse_clean_tuple (hgood : GoodTuples process h t ω)
    (L : Finset (AffineLine F)) (a : LineTuple F t)
    (ha : AdmissibleTuple process.shapes D h a)
    (hclean : ∀ i, a i ∈ cleanLines ω L)
    (hsmall : ((process.survivorSet ω ∩ crossPoints a).card : ℝ) <
      δ * (t : ℝ) ^ 2 / 2) : False :=
  (not_lt_of_ge (hgood.clean_crosscard_ge L a ha hclean)) hsmall

end GoodTuples

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

theorem filter_incidence_eq_inter (X : Finset (Point F)) (l : AffineLine F) :
    (X.filter fun x => Incidence x l) = X ∩ linePoints l := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, mem_linePoints]

theorem sdiff_coveredPoints_eq (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    X \ coveredPoints Incidence X L = X \ L.biUnion linePoints := by
  rw [coveredPoints_eq_inter_biUnion]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun h => hn ⟨hx, h⟩⟩
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun h => hn h.2⟩

theorem survivors_ignore_clean_line_eq (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) {l : AffineLine F} (hl : l ∈ cleanLines ω L) :
    survivors {linePoints l} ω = survivors ∅ ω := by
  simpa only [Finset.insert_empty] using
    (survivors_insert_eq_of_not_selected (ignore := ∅)
      (cleanLines_not_selected hl))

theorem clean_cover_count_bounds (ω : Fin n → Outcome shapes D)
    (L : Finset (AffineLine F)) (τ δ e0 e1 b : ℝ)
    (hδ : 0 < δ) (hτ : δ ≤ τ) (he1 : 0 ≤ e1)
    (htotal : τ * (Fintype.card F : ℝ) ^ 2 - e0 ≤ (survivors ∅ ω).card)
    (hlines : ∀ l : AffineLine F,
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ) ≤
        τ * (Fintype.card F : ℝ) + e1)
    (hmiss : ((survivors ∅ ω \ L.biUnion linePoints).card : ℝ) ≤ b)
    (hcard : L.card ≤ Fintype.card F) :
    (overlapExcess Incidence (survivors ∅ ω) (cleanLines ω L) : ℝ) ≤
        e0 + (Fintype.card F : ℝ) * e1 + b ∧
      (Fintype.card F : ℝ) - (cleanLines ω L).card ≤
        (e0 + (Fintype.card F : ℝ) * e1 + b) / (δ * Fintype.card F) := by
  have hq : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := F)
  apply cover_count_bounds Incidence (survivors ∅ ω) (cleanLines ω L)
    τ (Fintype.card F) e0 e1 b δ hδ hτ hq he1 htotal
  · intro l hl
    have hfilter :
        @Finset.filter _ (fun x => Incidence x l)
          (fun x => Classical.propDecidable (Incidence x l)) (survivors ∅ ω) =
          (survivors ∅ ω).filter (fun x => Incidence x l) :=
      Finset.filter_congr_decidable _ _ _
    rw [hfilter, filter_incidence_eq_inter, ← survivors_ignore_clean_line_eq ω L hl]
    exact hlines l
  · rw [sdiff_coveredPoints_eq, ← survivors_sdiff_cleanLines]
    exact hmiss
  · exact_mod_cast (Finset.card_le_card (cleanLines_subset ω L)).trans hcard

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [DecidableEq F]

def projectivePointsOf (X : Finset (Point F)) : Finset (ProjectivePoint F) :=
  X.image Sum.inl

def projectiveLinesOf (L : Finset (AffineLine F)) : Finset (ProjectiveLine F) :=
  L.image some

@[simp] theorem card_projectivePointsOf (X : Finset (Point F)) :
    (projectivePointsOf X).card = X.card := let _ := instFieldF; let _ := instFintypeF;
  Finset.card_image_of_injective X Sum.inl_injective

@[simp] theorem card_projectiveLinesOf (L : Finset (AffineLine F)) :
    (projectiveLinesOf L).card = L.card := let _ := instFieldF; let _ := instFintypeF;
  Finset.card_image_of_injective L (Option.some_injective _)

theorem leftDegree_projectiveLinesOf (L : Finset (AffineLine F)) (x : Point F) :
    Incidence.leftDegree ProjectiveIncidence (projectiveLinesOf L) (Sum.inl x) =
      multiplicity Incidence L x := let _ := instFintypeF; by
  unfold Incidence.leftDegree projectiveLinesOf multiplicity
  have houter :
      @Finset.filter _ (ProjectiveIncidence (Sum.inl x))
        (fun l => Classical.propDecidable (ProjectiveIncidence (Sum.inl x) l))
        (L.image some) = (L.image some).filter (ProjectiveIncidence (Sum.inl x)) :=
    Finset.filter_congr_decidable _ _ _
  have hinner :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [houter, hinner, Finset.filter_image, Finset.card_image_of_injective _ (Option.some_injective _)]
  congr 1

theorem incidenceCount_projective_lifts (X : Finset (Point F))
    (L : Finset (AffineLine F)) :
    Incidence.incidenceCount ProjectiveIncidence (projectivePointsOf X)
      (projectiveLinesOf L) = ∑ x ∈ X, multiplicity Incidence L x := by
  unfold Incidence.incidenceCount projectivePointsOf
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun x _ => leftDegree_projectiveLinesOf L x)
  · intro x hx y hy hxy
    exact Sum.inl.inj hxy

theorem multiplicity_eq_finite_pencil (L : Finset (AffineLine F)) (x : Point F) :
    multiplicity Incidence L x =
      (L.filter fun l => ProjectiveIncidence (Sum.inl x) (some l)).card := let _ := instFintypeF; by
  unfold multiplicity
  have hfilter :
      @Finset.filter _ (Incidence x) (fun l => Classical.propDecidable (Incidence x l)) L =
        L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  congr 1

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open Filter Topology

theorem savingExponent_lt_tenth : savingExponent < 1 / 10 := by
  norm_num [savingExponent]

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section

alias uniform_incidence_bound := uniform_incidence_bound_oddExt

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem heavy_incidence_sum_le
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T : ℝ)
    (hheavy : ((heavyPoints Incidence X L T).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent))
    (hL : L.card ≤ Fintype.card F) :
    (∑ x ∈ heavyPoints Incidence X L T, (multiplicity Incidence L x : ℝ)) ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - Incidence.savingExponent) := by
  have hqone : 1 ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := F)))
  have hqpow : (Fintype.card F : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hqone
        (show (1 : ℝ) ≤ 1 + Incidence.savingExponent by
          linarith [Incidence.savingExponent_pos]))
  have hbound := Incidence.uniform_incidence_bound F hq hsub
    (projectivePointsOf (heavyPoints Incidence X L T)) (projectiveLinesOf L)
    (by simpa only [card_projectivePointsOf] using hheavy)
    (by
      rw [card_projectiveLinesOf]
      exact (show (L.card : ℝ) ≤ (Fintype.card F : ℝ) by
        exact_mod_cast hL).trans hqpow)
  rw [incidenceCount_projective_lifts, Nat.cast_sum] at hbound
  exact hbound

theorem orderedPairMass_le_of_uniform_incidence
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T R : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hheavy : ((heavyPoints Incidence X L T).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent))
    (hL : L.card ≤ Fintype.card F)
    (hpencil : ∀ p : ProjectivePoint F, ((coverPencil L p).card : ℝ) ≤ R) :
    (orderedPairMass Incidence X L : ℝ) ≤
      T * (overlapExcess Incidence X L : ℝ) +
        R * (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - Incidence.savingExponent) := by
  have hpoint : ∀ x ∈ X, (multiplicity Incidence L x : ℝ) ≤ R := by
    intro x _
    rw [multiplicity_eq_finite_pencil]
    simpa only [coverPencil] using hpencil (Sum.inl x)
  exact (orderedPairMass_le_light_add_heavy Incidence X L T R hT hpoint).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (heavy_incidence_sum_le hq hsub X L T hheavy hL) hR))

theorem heavyPoints_card_le_of_excess
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T B : ℝ)
    (hT : 1 < T) (hE : (overlapExcess Incidence X L : ℝ) ≤ B) :
    ((heavyPoints Incidence X L T).card : ℝ) ≤ B / (T - 1) := let _ := instFintypeF; by
  apply (le_div_iff₀ (sub_pos.mpr hT)).2
  exact (heavyPoints_card_mul_le_excess Incidence X L T hT).trans hE

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exists_max_coverPencil (L : Finset (AffineLine F)) :
    ∃ p : ProjectivePoint F, ∀ r : ProjectivePoint F,
      (coverPencil L r).card ≤ (coverPencil L p).card := by
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ProjectivePoint F))
    (fun p => (coverPencil L p).card)
    ⟨Sum.inr none, Finset.mem_univ _⟩
  exact ⟨p, fun r => hp r (Finset.mem_univ r)⟩

def maxCenter (L : Finset (AffineLine F)) : ProjectivePoint F :=
  Classical.choose (exists_max_coverPencil L)

def maxConcurrency (L : Finset (AffineLine F)) : ℕ :=
  (coverPencil L (maxCenter L)).card

theorem coverPencil_card_le_maxConcurrency (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : (coverPencil L p).card ≤ maxConcurrency L :=
  Classical.choose_spec (exists_max_coverPencil L) p

theorem card_complement_add_card_coverPencil (L : Finset (AffineLine F))
    (p : ProjectivePoint F) :
    (L \ coverPencil L p).card + (coverPencil L p).card = L.card :=
  Finset.card_sdiff_add_card_eq_card (coverPencil_subset L p)

theorem complement_card_ge_half_of_count_bounds
    (L : Finset (AffineLine F)) (p : ProjectivePoint F) (q ρ b δ : ℝ)
    (hcount : q - b / (δ * q) ≤ (L.card : ℝ))
    (herror : b / (δ * q) ≤ ρ * q / 2)
    (hp : ((coverPencil L p).card : ℝ) < (1 - ρ) * q) :
    ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) := by
  have hsum : ((L \ coverPencil L p).card : ℝ) +
      ((coverPencil L p).card : ℝ) = (L.card : ℝ) := by
    exact_mod_cast card_complement_add_card_coverPencil L p
  nlinarith

theorem complement_card_ge_half_of_no_large_pencil
    (L : Finset (AffineLine F)) (q ρ b δ : ℝ)
    (hcount : q - b / (δ * q) ≤ (L.card : ℝ))
    (herror : b / (δ * q) ≤ ρ * q / 2)
    (hsmall : ∀ p : ProjectivePoint F,
      ((coverPencil L p).card : ℝ) < (1 - ρ) * q)
    (p : ProjectivePoint F) :
    ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) :=
  complement_card_ge_half_of_count_bounds L p q ρ b δ hcount herror (hsmall p)

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

abbrev CoverSample (L : Finset (AffineLine F)) (t : ℕ) :=
  (Fin t ⊕ Fin t) ↪ ↥L

def liftSample (L : Finset (AffineLine F)) {t : ℕ} (u : CoverSample L t) :
    LineTuple F t :=
  u.trans ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem liftSample_apply (L : Finset (AffineLine F)) {t : ℕ}
    (u : CoverSample L t) (i : Fin t ⊕ Fin t) :
    liftSample L u i = (u i).val := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; rfl

theorem liftSample_mem (L : Finset (AffineLine F)) {t : ℕ}
    (u : CoverSample L t) (i : Fin t ⊕ Fin t) : liftSample L u i ∈ L := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF;
  (u i).property

def CrossHit (X : Finset (Point F)) {t : ℕ} (a : LineTuple F t)
    (p : Fin t × Fin t) : Prop :=
  ∃ x ∈ X, Incidence x (a (Sum.inl p.1)) ∧ Incidence x (a (Sum.inr p.2))

def crossHitCount (X : Finset (Point F)) {t : ℕ} (a : LineTuple F t) : ℕ :=
  (Finset.univ.filter (CrossHit X a)).card

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F]

def survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    Finset (AffineLine F × AffineLine F) :=
  X.biUnion fun x => (L.filter (Incidence x)).offDiag

theorem mem_survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (a b : AffineLine F) :
    (a, b) ∈ survivorPairs X L ↔
      a ∈ L ∧ b ∈ L ∧ a ≠ b ∧ ∃ x ∈ X, Incidence x a ∧ Incidence x b := by
  simp only [survivorPairs, Finset.mem_biUnion, Finset.mem_offDiag,
    Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, ⟨ha, hxa⟩, ⟨hb, hxb⟩, hab⟩
    exact ⟨ha, hb, hab, x, hx, hxa, hxb⟩
  · rintro ⟨ha, hb, hab, x, hx, hxa, hxb⟩
    exact ⟨x, hx, ⟨ha, hxa⟩, ⟨hb, hxb⟩, hab⟩

theorem survivorPairs_fibers_disjoint
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (X : Set (Point F)).PairwiseDisjoint
      (fun x => (L.filter (Incidence x)).offDiag) := by
  intro x _ y _ hxy
  apply Finset.disjoint_left.mpr
  intro p hx hy
  obtain ⟨hxa, hxb, hab⟩ := Finset.mem_offDiag.mp hx
  obtain ⟨hya, hyb, _⟩ := Finset.mem_offDiag.mp hy
  apply hxy
  exact eq_of_common_incidence_of_ne_lines hab
    (Finset.mem_filter.mp hxa).2 (Finset.mem_filter.mp hxb).2
    (Finset.mem_filter.mp hya).2 (Finset.mem_filter.mp hyb).2

theorem card_survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (survivorPairs X L).card =
      ∑ x ∈ X, (L.filter (Incidence x)).card *
        ((L.filter (Incidence x)).card - 1) := by
  rw [survivorPairs, Finset.card_biUnion (survivorPairs_fibers_disjoint X L)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]

theorem card_survivorPairs_eq_orderedPairMass
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (survivorPairs X L).card = orderedPairMass Incidence X L := by
  rw [card_survivorPairs]
  unfold orderedPairMass multiplicity
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun n : ℕ => n * (n - 1))
  apply congrArg Finset.card
  ext l
  simp only [Finset.mem_filter]

def populationSurvivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    Finset (↥L × ↥L) :=
  Finset.univ.filter fun p => (p.1.val, p.2.val) ∈ survivorPairs X L

theorem mem_populationSurvivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ↥L × ↥L) :
    p ∈ populationSurvivorPairs X L ↔
      p.1 ≠ p.2 ∧ ∃ x ∈ X, Incidence x p.1.val ∧ Incidence x p.2.val := by
  simp only [populationSurvivorPairs, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_survivorPairs, p.1.property, p.2.property]
  exact and_congr (not_congr Subtype.val_inj) Iff.rfl

theorem card_populationSurvivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (populationSurvivorPairs X L).card = (survivorPairs X L).card := by
  apply Finset.card_bij (fun p _ => (p.1.val, p.2.val))
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p _ q _ hpq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpq)
    · exact Subtype.ext (congrArg Prod.snd hpq)
  · intro p hp
    have hm := (mem_survivorPairs X L p.1 p.2).mp hp
    refine ⟨(⟨p.1, hm.1⟩, ⟨p.2, hm.2.1⟩), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

theorem card_populationSurvivorPairs_eq_orderedPairMass
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (populationSurvivorPairs X L).card = orderedPairMass Incidence X L := by
  rw [card_populationSurvivorPairs, card_survivorPairs_eq_orderedPairMass]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

universe u v w

def restrict {I : Type u} {J : Type v} {Ω : Type w}
    (j : I ↪ J) (sample : J ↪ Ω) : I ↪ Ω :=
  j.trans sample

@[simp] theorem restrict_apply {I : Type u} {J : Type v} {Ω : Type w}
    (j : I ↪ J) (sample : J ↪ Ω) (i : I) :
    restrict j sample i = sample (j i) := rfl

theorem restriction_fiber_natCard_eq
    {I : Type u} {J : Type v} {Ω : Type w} [Finite I]
    (j : I ↪ J) (v₀ v₁ : I ↪ Ω) :
    Nat.card {sample : J ↪ Ω // restrict j sample = v₀} =
      Nat.card {sample : J ↪ Ω // restrict j sample = v₁} := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    v₀ v₁ v₀.injective v₁.injective
  let E : (J ↪ Ω) ≃ (J ↪ Ω) :=
    Equiv.embeddingCongr (Equiv.refl J) σ
  refine Nat.card_congr
    (E.subtypeEquiv
      (p := fun sample => restrict j sample = v₀)
      (q := fun sample => restrict j sample = v₁) ?_)
  intro sample
  constructor
  · intro hu
    apply Function.Embedding.ext
    intro i
    change σ (sample (j i)) = v₁ i
    have hi := congrArg (fun b : I ↪ Ω => b i) hu
    change sample (j i) = v₀ i at hi
    exact (congrArg σ hi).trans (hσ i)
  · intro hu
    apply Function.Embedding.ext
    intro i
    change sample (j i) = v₀ i
    apply σ.injective
    have hi := congrArg (fun b : I ↪ Ω => b i) hu
    change σ (sample (j i)) = v₁ i at hi
    exact hi.trans (hσ i).symm

theorem natCard_embeddings
    {A : Type u} {B : Type v} [Finite A] [Finite B] :
    Nat.card (A ↪ B) =
      (Nat.card B).descFactorial (Nat.card A) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_embedding_eq (α := A) (β := B))

section Laws

variable {I : Type u} {J : Type v} {Ω : Type w}
  [Fintype I] [Fintype J] [Fintype Ω]

theorem map_uniform_restrict [Nonempty (J ↪ Ω)] [Nonempty (I ↪ Ω)]
    (j : I ↪ J) :
    (FiniteLaw.uniform (J ↪ Ω)).map (restrict j) =
      FiniteLaw.uniform (I ↪ Ω) :=
  FiniteLaw.map_uniform_of_fiber_card_eq (restrict j)
    (restriction_fiber_natCard_eq j)

theorem prob_restrict [Nonempty (J ↪ Ω)] [Nonempty (I ↪ Ω)]
    (j : I ↪ J) (P : (I ↪ Ω) → Prop) :
    (FiniteLaw.uniform (J ↪ Ω)).prob (fun sample => P (restrict j sample)) =
      (FiniteLaw.uniform (I ↪ Ω)).prob P := by
  calc
    _ = ((FiniteLaw.uniform (J ↪ Ω)).map (restrict j)).prob P :=
      (FiniteLaw.prob_map _ _ _).symm
    _ = _ := by rw [map_uniform_restrict j]

theorem map_uniform_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω] (i : I) :
    (FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i) =
      FiniteLaw.uniform Ω := by
  classical
  apply FiniteLaw.map_uniform_of_fiber_card_eq
  intro a b
  let E : (I ↪ Ω) ≃ (I ↪ Ω) :=
    Equiv.embeddingCongr (Equiv.refl I) (Equiv.swap a b)
  refine Nat.card_congr
    (E.subtypeEquiv
      (p := fun sample => sample i = a)
      (q := fun sample => sample i = b) ?_)
  intro sample
  change sample i = a ↔ Equiv.swap a b (sample i) = b
  constructor
  · intro hu
    rw [hu, Equiv.swap_apply_left]
  · intro hu
    apply (Equiv.swap a b).injective
    simpa only [Equiv.swap_apply_left] using hu

theorem prob_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω]
    (i : I) (P : Ω → Prop) :
    (FiniteLaw.uniform (I ↪ Ω)).prob (fun sample => P (sample i)) =
      (FiniteLaw.uniform Ω).prob P := by
  calc
    _ = ((FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i)).prob P :=
      (FiniteLaw.prob_map _ _ _).symm
    _ = _ := by rw [map_uniform_coordinate i]

theorem expectation_coordinate [Nonempty (I ↪ Ω)] [Nonempty Ω]
    (i : I) (f : Ω → ℝ) :
    (FiniteLaw.uniform (I ↪ Ω)).expectation (fun sample => f (sample i)) =
      (FiniteLaw.uniform Ω).expectation f := by
  calc
    _ = ((FiniteLaw.uniform (I ↪ Ω)).map (fun sample => sample i)).expectation f :=
      (FiniteLaw.expectation_map _ _ _).symm
    _ = _ := by rw [map_uniform_coordinate i]

end Laws

theorem sample_nonempty (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) : Nonempty (I ↪ Ω) :=
  Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card] using hle)

noncomputable def law (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) : FiniteLaw (I ↪ Ω) := by
  letI : Nonempty (I ↪ Ω) := sample_nonempty I Ω hle
  exact FiniteLaw.uniform (I ↪ Ω)

theorem law_eq_uniform (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    [Nonempty (I ↪ Ω)] (hle : Nat.card I ≤ Nat.card Ω) :
    law I Ω hle = FiniteLaw.uniform (I ↪ Ω) := rfl

theorem law_prob (I : Type u) (Ω : Type v) [Fintype I] [Fintype Ω]
    (hle : Nat.card I ≤ Nat.card Ω) (P : (I ↪ Ω) → Prop) :
    (law I Ω hle).prob P =
      (Nat.card {sample : I ↪ Ω // P sample} : ℝ) /
        ((Nat.card Ω).descFactorial (Nat.card I) : ℝ) := by
  classical
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hle
  simpa only [law_eq_uniform, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_embedding_eq] using
    (FiniteLaw.uniform_prob (I ↪ Ω) P)

variable {I : Type u} {J : Type v} {Ω : Type w}
  [Fintype I] [Fintype J] [Fintype Ω]

theorem prob_law_restrict (j : I ↪ J)
    (hJ : Nat.card J ≤ Nat.card Ω) (hI : Nat.card I ≤ Nat.card Ω)
    (P : (I ↪ Ω) → Prop) :
    (law J Ω hJ).prob (fun sample => P (restrict j sample)) =
      (law I Ω hI).prob P := by
  let : Nonempty (J ↪ Ω) := sample_nonempty J Ω hJ
  let : Nonempty (I ↪ Ω) := sample_nonempty I Ω hI
  simpa only [law_eq_uniform] using (prob_restrict j P)

end RyserCoveringCounterexample.InjectionSampling

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

theorem card_disjoint_pair_assignments_le
    {Ω : Type*} [Fintype Ω] (B : Finset (Ω × Ω)) (h : ℕ) :
    Fintype.card {u : (Fin h ⊕ Fin h) ↪ Ω //
      ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B} ≤ B.card ^ h := by
  classical
  let encode : {u : (Fin h ⊕ Fin h) ↪ Ω //
      ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B} → (Fin h → ↥B) :=
    fun u k => ⟨(u.val (Sum.inl k), u.val (Sum.inr k)), u.property k⟩
  have hencode : Function.Injective encode := by
    intro u v huv
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    cases slot with
    | inl k => exact congrArg (fun f : Fin h → ↥B => (f k).val.1) huv
    | inr k => exact congrArg (fun f : Fin h → ↥B => (f k).val.2) huv
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hencode

theorem prob_disjoint_pairs_le
    {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty (I ↪ Ω)]
    {h : ℕ} (j : (Fin h ⊕ Fin h) ↪ I) (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform (I ↪ Ω)).prob
        (fun u => ∀ k, (u (j (Sum.inl k)), u (j (Sum.inr k))) ∈ B) ≤
      (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  classical
  let : Nonempty ((Fin h ⊕ Fin h) ↪ Ω) :=
    ⟨j.trans (Classical.choice (inferInstance : Nonempty (I ↪ Ω)))⟩
  let P : ((Fin h ⊕ Fin h) ↪ Ω) → Prop :=
    fun u => ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B
  change (FiniteLaw.uniform (I ↪ Ω)).prob (fun u => P (restrict j u)) ≤ _
  rw [prob_restrict j P, FiniteLaw.uniform_prob]
  have hfilter :
      @Finset.filter _ P (fun sample => Classical.propDecidable (P sample))
          Finset.univ = Finset.univ.filter P :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  have hnat : (Finset.univ.filter P).card ≤ B.card ^ h := by
    simpa only [Fintype.card_subtype] using card_disjoint_pair_assignments_le B h
  have hreal : ((Finset.univ.filter P).card : ℝ) ≤ ((B.card ^ h : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_pow] at hreal
  calc
    _ ≤ (B.card : ℝ) ^ h / Fintype.card ((Fin h ⊕ Fin h) ↪ Ω) :=
      div_le_div_of_nonneg_right hreal (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Fintype.card_embedding_eq, Fintype.card_sum, Fintype.card_fin,
        ← Nat.two_mul]

theorem prob_exists_disjoint_pairs_descFactorial_le
    {Ω : Type*} [Fintype Ω] {h t : ℕ}
    [Nonempty ((Fin t ⊕ Fin t) ↪ Ω)] (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)).prob
        (fun u => ∃ left right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) ≤
      (t.descFactorial h : ℝ) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)
  calc
    _ ≤ ∑ left : Fin h ↪ Fin t,
        μ.prob (fun u => ∃ right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) :=
      μ.prob_exists_le _
    _ ≤ ∑ left : Fin h ↪ Fin t, ∑ right : Fin h ↪ Fin t,
        μ.prob (fun u =>
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) := by
      apply Finset.sum_le_sum
      intro left _
      exact μ.prob_exists_le _
    _ ≤ ∑ _left : Fin h ↪ Fin t, ∑ _right : Fin h ↪ Fin t,
        (B.card : ℝ) ^ h /
          ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
      apply Finset.sum_le_sum
      intro left _
      apply Finset.sum_le_sum
      intro right _
      exact prob_disjoint_pairs_le (Function.Embedding.sumMap left right) B
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin]
      ring

theorem prob_exists_disjoint_pairs_le
    {Ω : Type*} [Fintype Ω] {h t : ℕ}
    [Nonempty ((Fin t ⊕ Fin t) ↪ Ω)] (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)).prob
        (fun u => ∃ left right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) ≤
      (t : ℝ) ^ (2 * h) * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  have hslots : (t.descFactorial h : ℝ) ≤ (t : ℝ) ^ h := by
    have hcast : (t.descFactorial h : ℝ) ≤ ((t ^ h : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.descFactorial_le_pow t h)
    simpa only [Nat.cast_pow] using hcast
  calc
    _ ≤ (t.descFactorial h : ℝ) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) :=
      prob_exists_disjoint_pairs_descFactorial_le B
    _ ≤ ((t : ℝ) ^ h) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hslots 2)
        (pow_nonneg (Nat.cast_nonneg _) h)
    _ = _ := by rw [← pow_mul, Nat.mul_comm h 2]

end RyserCoveringCounterexample.InjectionSampling

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

theorem card_cross_survivors_le_hitCount (X : Finset (Point F))
    {t : ℕ} (a : LineTuple F t) :
    (X ∩ crossPoints a).card ≤ crossHitCount X a := by
  classical
  let S := X ∩ crossPoints a
  have hex (x : ↥S) : ∃ p : Fin t × Fin t,
      Incidence x.val (a (Sum.inl p.1)) ∧ Incidence x.val (a (Sum.inr p.2)) := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints a x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep (x : ↥S) : Fin t × Fin t := Classical.choose (hex x)
  have hrep (x : ↥S) :
      Incidence x.val (a (Sum.inl (rep x).1)) ∧
        Incidence x.val (a (Sum.inr (rep x).2)) := Classical.choose_spec (hex x)
  let encode : ↥S → {p : Fin t × Fin t // CrossHit X a p} := fun x =>
    ⟨rep x, x.val, (Finset.mem_inter.mp x.property).1, (hrep x).1, (hrep x).2⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hp : rep x = rep y := congrArg Subtype.val hxy
    apply Subtype.ext
    exact eq_of_common_incidence_of_ne_lines (left_ne_right a (rep x).1 (rep x).2)
      (hrep x).1 (hrep x).2
      (by simpa only [hp] using (hrep y).1)
      (by simpa only [hp] using (hrep y).2)
  calc
    (X ∩ crossPoints a).card = Fintype.card ↥S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card {p : Fin t × Fin t // CrossHit X a p} :=
      Fintype.card_le_of_injective encode hinj
    _ = crossHitCount X a := by
      rw [Fintype.card_subtype]
      unfold crossHitCount
      apply congrArg Finset.card
      ext p
      simp only [Finset.mem_filter]

theorem crossHitCount_eq_sum (X : Finset (Point F)) {t : ℕ}
    (a : LineTuple F t) :
    (crossHitCount X a : ℝ) =
      ∑ p : Fin t × Fin t, if CrossHit X a p then (1 : ℝ) else 0 := let _ := instFintypeF; let _ := instDecidableEqF; by
  exact Finset.natCast_card_filter (CrossHit X a) Finset.univ

theorem prob_crossHit_le (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] (p : Fin t × Fin t) :
    (FiniteLaw.uniform (CoverSample L t)).prob
        (fun u => CrossHit X (liftSample L u) p) ≤
      (orderedPairMass Incidence X L : ℝ) / (L.card.descFactorial 2 : ℝ) := let _ := instFintypeF; let _ := instDecidableEqF; by
  classical
  let left : Fin 1 ↪ Fin t := ⟨fun _ => p.1, fun _ _ _ => Subsingleton.elim _ _⟩
  let right : Fin 1 ↪ Fin t := ⟨fun _ => p.2, fun _ _ _ => Subsingleton.elim _ _⟩
  have h := InjectionSampling.prob_disjoint_pairs_le
    (Function.Embedding.sumMap left right) (populationSurvivorPairs X L)
  have hevent :
      (fun u : CoverSample L t => ∀ k : Fin 1,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ populationSurvivorPairs X L) =
        (fun u => CrossHit X (liftSample L u) p) := by
    funext u
    apply propext
    have hne : u (Sum.inl p.1) ≠ u (Sum.inr p.2) := by
      intro heq
      exact Sum.inl_ne_inr (u.injective heq)
    change (∀ _k : Fin 1,
      (u (Sum.inl p.1), u (Sum.inr p.2)) ∈ populationSurvivorPairs X L) ↔ _
    constructor
    · intro hu
      exact ((mem_populationSurvivorPairs X L _).mp (hu 0)).2
    · intro hu _k
      exact (mem_populationSurvivorPairs X L _).mpr ⟨hne, hu⟩
  change (FiniteLaw.uniform (CoverSample L t)).prob
      (fun u => ∀ k : Fin 1,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ populationSurvivorPairs X L) ≤ _ at h
  rw [hevent] at h
  simpa only [pow_one, Nat.mul_one, Fintype.card_coe,
    card_populationSurvivorPairs_eq_orderedPairMass] using h

theorem expectation_crossHitCount_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] :
    (FiniteLaw.uniform (CoverSample L t)).expectation
        (fun u => (crossHitCount X (liftSample L u) : ℝ)) ≤
      (t : ℝ) ^ 2 * (orderedPairMass Incidence X L : ℝ) /
        (L.card.descFactorial 2 : ℝ) := by
  let μ := FiniteLaw.uniform (CoverSample L t)
  calc
    _ = μ.expectation (fun u => ∑ p : Fin t × Fin t,
        if CrossHit X (liftSample L u) p then (1 : ℝ) else 0) := by
      congr 1
      funext u
      exact crossHitCount_eq_sum X (liftSample L u)
    _ = ∑ p : Fin t × Fin t, μ.expectation
        (fun u => if CrossHit X (liftSample L u) p then (1 : ℝ) else 0) :=
      μ.expectation_sum _
    _ = ∑ p : Fin t × Fin t, μ.prob (fun u => CrossHit X (liftSample L u) p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (μ.prob_eq_expectation _).symm
    _ ≤ ∑ _p : Fin t × Fin t,
        (orderedPairMass Incidence X L : ℝ) / (L.card.descFactorial 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      exact prob_crossHit_le X L p
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

theorem prob_many_cross_survivors_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    {t : ℕ} [Nonempty (CoverSample L t)] {δ : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    (FiniteLaw.uniform (CoverSample L t)).prob
        (fun u => δ * (t : ℝ) ^ 2 / 2 ≤
          ((X ∩ crossPoints (liftSample L u)).card : ℝ)) ≤
      2 * (orderedPairMass Incidence X L : ℝ) /
        (δ * (L.card.descFactorial 2 : ℝ)) := by
  let μ := FiniteLaw.uniform (CoverSample L t)
  have htR : 0 < (t : ℝ) := Nat.cast_pos.mpr ht
  have hthreshold : 0 < δ * (t : ℝ) ^ 2 / 2 := by positivity
  calc
    _ ≤ μ.prob (fun u => δ * (t : ℝ) ^ 2 / 2 ≤
        (crossHitCount X (liftSample L u) : ℝ)) := by
      apply μ.prob_mono
      intro u hu
      exact hu.trans (Nat.cast_le.mpr (card_cross_survivors_le_hitCount X _))
    _ ≤ μ.expectation (fun u => (crossHitCount X (liftSample L u) : ℝ)) /
        (δ * (t : ℝ) ^ 2 / 2) :=
      μ.prob_ge_le_expectation_div _ (fun _ => Nat.cast_nonneg _) hthreshold
    _ ≤ ((t : ℝ) ^ 2 * (orderedPairMass Incidence X L : ℝ) /
        (L.card.descFactorial 2 : ℝ)) / (δ * (t : ℝ) ^ 2 / 2) :=
      div_le_div_of_nonneg_right (expectation_crossHitCount_le X L) hthreshold.le
    _ = _ := by
      by_cases hden : (L.card.descFactorial 2 : ℝ) = 0
      · simp only [hden, div_zero, mul_zero, zero_div]
      · field_simp [hδ.ne', htR.ne', hden]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.LowDegeneracy

open InjectionSampling

private theorem natCard_le_mul_of_fibers
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (R : ℕ)
    (h : ∀ b, Nat.card {a : A // f a = b} ≤ R) :
    Nat.card A ≤ Nat.card B * R := by
  classical
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
      exact Nat.card_sigma
    _ ≤ ∑ _b : B, R := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * R := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Nat.card_eq_fintype_card]

variable {F : Type*} [instFieldF : Field F] [instDecidableEqF : DecidableEq F]

def SameDirection {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) : Prop :=
  (u 0).val.1 = (u 1).val.1

def Concurrent {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) : Prop :=
  ∃ p : ProjectivePoint F, ∀ i, ProjectiveIncidence p (some (u i).val)

def firstPair {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) : Fin 2 ↪ ↥L :=
  (Fin.castLEEmb (by decide : 2 ≤ 3)).trans u

@[simp] theorem firstPair_zero {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) :
    firstPair u 0 = u 0 := let _ := instFieldF; let _ := instDecidableEqF; rfl

@[simp] theorem firstPair_one {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) :
    firstPair u 1 = u 1 := let _ := instFieldF; let _ := instDecidableEqF; rfl

private theorem pair_lines_ne {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) :
    (u 0).val ≠ (u 1).val := let _ := instFieldF; let _ := instDecidableEqF; by
  intro h
  have h01 : (0 : Fin 2) = 1 := u.injective (Subtype.ext h)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

def pairMeet {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) : ProjectivePoint F :=
  Classical.choose (existsUnique_projective_incident_of_ne_lines (pair_lines_ne u))

theorem eq_pairMeet {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L)
    {p : ProjectivePoint F}
    (h0 : ProjectiveIncidence p (some (u 0).val))
    (h1 : ProjectiveIncidence p (some (u 1).val)) : p = pairMeet u :=
  (Classical.choose_spec
    (existsUnique_projective_incident_of_ne_lines (pair_lines_ne u))).2 p ⟨h0, h1⟩

theorem card_sameDirection_le (L : Finset (AffineLine F)) (R : ℕ)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    Nat.card {u : Fin 2 ↪ ↥L // SameDirection u} ≤ L.card * R := let _ := instFieldF; by
  classical
  let A := {u : Fin 2 ↪ ↥L // SameDirection u}
  let f : A → ↥L := fun u => u.val 0
  have hf : ∀ l, Nat.card {u : A // f u = l} ≤ R := by
    intro l
    let g : {u : A // f u = l} → ↥(L.filter fun k => k.1 = l.val.1) :=
      fun u => ⟨(u.val.val 1).val, Finset.mem_filter.mpr
        ⟨(u.val.val 1).property,
          u.val.property.symm.trans
            (congrArg (fun k : ↥L => k.val.1) u.property)⟩⟩
    have hg : Function.Injective g := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact u.property.trans v.property.symm
      · apply Subtype.ext
        exact congrArg (fun z : ↥(L.filter fun k => k.1 = l.val.1) => z.val) huv
    exact (Nat.card_le_card_of_injective g hg).trans
      (by simpa only [Nat.card_eq_finsetCard] using hR l.val.1)
  simpa only [Nat.card_eq_finsetCard] using natCard_le_mul_of_fibers f R hf

theorem card_concurrent_le (L : Finset (AffineLine F)) (R : ℕ)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    Nat.card {u : Fin 3 ↪ ↥L // Concurrent u} ≤
      L.card.descFactorial 2 * R := by
  classical
  let A := {u : Fin 3 ↪ ↥L // Concurrent u}
  let f : A → (Fin 2 ↪ ↥L) := fun u => firstPair u.val
  have hf : ∀ e, Nat.card {u : A // f u = e} ≤ R := by
    intro e
    let g : {u : A // f u = e} →
        ↥(L.filter fun l => ProjectiveIncidence (pairMeet e) (some l)) :=
      fun u => ⟨(u.val.val 2).val, by
        refine Finset.mem_filter.mpr ⟨(u.val.val 2).property, ?_⟩
        obtain ⟨p, hp⟩ := u.val.property
        have h0 : u.val.val 0 = e 0 :=
          congrArg (fun b : Fin 2 ↪ ↥L => b 0) u.property
        have h1 : u.val.val 1 = e 1 :=
          congrArg (fun b : Fin 2 ↪ ↥L => b 1) u.property
        have heq : p = pairMeet e := eq_pairMeet e
          (by rw [← h0]; exact hp 0) (by rw [← h1]; exact hp 1)
        exact heq ▸ hp 2⟩
    have hg : Function.Injective g := by
      intro u v huv
      have he : firstPair u.val.val = firstPair v.val.val :=
        u.property.trans v.property.symm
      apply Subtype.ext
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact congrArg (fun b : Fin 2 ↪ ↥L => b 0) he
      · exact congrArg (fun b : Fin 2 ↪ ↥L => b 1) he
      · apply Subtype.ext
        exact congrArg (fun z :
          ↥(L.filter fun l => ProjectiveIncidence (pairMeet e) (some l)) => z.val) huv
    exact (Nat.card_le_card_of_injective g hg).trans
      (by simpa only [Nat.card_eq_finsetCard] using hR (pairMeet e))
  simpa only [natCard_embeddings, Nat.card_fin, Nat.card_eq_finsetCard] using
    natCard_le_mul_of_fibers f R hf

private theorem prob_le_of_card
    {Ω : Type*} [Fintype Ω] (k R : ℕ)
    (hle : Nat.card (Fin (k + 1)) ≤ Nat.card Ω)
    (P : (Fin (k + 1) ↪ Ω) → Prop)
    (hcard : Nat.card {u : Fin (k + 1) ↪ Ω // P u} ≤
      (Nat.card Ω).descFactorial k * R) :
    (law (Fin (k + 1)) Ω hle).prob P ≤
      (R : ℝ) / ((Nat.card Ω - k : ℕ) : ℝ) := by
  have hk : k ≤ Nat.card Ω := by
    have h := hle
    rw [Nat.card_fin] at h
    omega
  have hn : ((Nat.card Ω).descFactorial k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne'
  rw [law_prob, Nat.card_fin]
  calc
    _ ≤ (((Nat.card Ω).descFactorial k * R : ℕ) : ℝ) /
        ((Nat.card Ω).descFactorial (k + 1) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = (R : ℝ) / ((Nat.card Ω - k : ℕ) : ℝ) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul]
      rw [mul_comm (((Nat.card Ω - k : ℕ) : ℝ))
        (((Nat.card Ω).descFactorial k : ℝ))]
      exact mul_div_mul_left _ _ hn

theorem prob_sameDirection_le (L : Finset (AffineLine F)) (R : ℕ)
    (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law (Fin 2) ↥L (by simpa using hL)).prob SameDirection ≤
      (R : ℝ) / ((L.card - 1 : ℕ) : ℝ) := by
  have hcard : Nat.card {u : Fin 2 ↪ ↥L // SameDirection u} ≤
      (Nat.card ↥L).descFactorial 1 * R := by
    simpa only [Nat.card_eq_finsetCard, Nat.descFactorial_one] using
      card_sameDirection_le L R hR
  simpa only [Nat.card_eq_finsetCard] using
    prob_le_of_card (Ω := ↥L) 1 R (by simpa using hL) SameDirection hcard

theorem prob_concurrent_le (L : Finset (AffineLine F)) (R : ℕ)
    (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law (Fin 3) ↥L (by simpa using hL)).prob Concurrent ≤
      (R : ℝ) / ((L.card - 2 : ℕ) : ℝ) := by
  have hcard : Nat.card {u : Fin 3 ↪ ↥L // Concurrent u} ≤
      (Nat.card ↥L).descFactorial 2 * R := by
    simpa only [Nat.card_eq_finsetCard] using card_concurrent_le L R hR
  simpa only [Nat.card_eq_finsetCard] using
    prob_le_of_card (Ω := ↥L) 2 R (by simpa using hL) Concurrent hcard

theorem prob_exists_restrict_le
    {I Ω : Type*} [Fintype I] [Fintype Ω] (k : ℕ)
    (hI : Nat.card I ≤ Nat.card Ω) (hk : Nat.card (Fin k) ≤ Nat.card Ω)
    (P : (Fin k ↪ Ω) → Prop) (B : ℝ)
    (hP : (law (Fin k) Ω hk).prob P ≤ B) :
    (law I Ω hI).prob (fun u => ∃ j : Fin k ↪ I, P (restrict j u)) ≤
      ((Nat.card I).descFactorial k : ℝ) * B := by
  classical
  calc
    _ ≤ ∑ j : Fin k ↪ I, (law I Ω hI).prob (fun u => P (restrict j u)) :=
      FiniteLaw.prob_exists_le _ _
    _ = ∑ _j : Fin k ↪ I, (law (Fin k) Ω hk).prob P := by
      apply Finset.sum_congr rfl
      intro j _
      exact prob_law_restrict j hI hk P
    _ ≤ ∑ _j : Fin k ↪ I, B := Finset.sum_le_sum (fun _ _ => hP)
    _ = ((Nat.card I).descFactorial k : ℝ) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin, Nat.card_eq_fintype_card]

def AnyParallel {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) : Prop :=
  ∃ j : Fin 2 ↪ I, SameDirection (restrict j u)

def AnyConcurrent {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) : Prop :=
  ∃ j : Fin 3 ↪ I, Concurrent (restrict j u)

theorem anyParallel_iff {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) :
    AnyParallel u ↔ ∃ i j, i ≠ j ∧ (u i).val.1 = (u j).val.1 := let _ := instFieldF; let _ := instDecidableEqF; by
  classical
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j 0, j 1, fun h => (by decide : (0 : Fin 2) ≠ 1) (j.injective h), hj⟩
  · rintro ⟨i, j, hij, hdir⟩
    let e : Fin 2 ↪ I :=
      { toFun := ![i, j]
        inj' := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all }
    exact ⟨e, hdir⟩

theorem anyConcurrent_iff {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) :
    AnyConcurrent u ↔ ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ∃ p : ProjectivePoint F,
        ProjectiveIncidence p (some (u i).val) ∧
        ProjectiveIncidence p (some (u j).val) ∧
        ProjectiveIncidence p (some (u k).val) := let _ := instDecidableEqF; by
  classical
  constructor
  · rintro ⟨j, p, hp⟩
    refine ⟨j 0, j 1, j 2, ?_, ?_, ?_, p, hp 0, hp 1, hp 2⟩
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (j.injective h)
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (j.injective h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (j.injective h)
  · rintro ⟨i, j, k, hij, hik, hjk, p, hi, hj, hk⟩
    let e : Fin 3 ↪ I :=
      { toFun := ![i, j, k]
        inj' := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all }
    refine ⟨e, p, ?_⟩
    intro a
    fin_cases a
    · exact hi
    · exact hj
    · exact hk

theorem prob_anyParallel_le {I : Type*} [Fintype I]
    (L : Finset (AffineLine F)) (R : ℕ)
    (hI : Nat.card I ≤ Nat.card ↥L) (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law I ↥L hI).prob AnyParallel ≤
      ((Nat.card I).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  have hevent : (AnyParallel : (I ↪ ↥L) → Prop) =
      (fun u => ∃ j : Fin 2 ↪ I, SameDirection (restrict j u)) := by
    funext u
    rfl
  rw [hevent]
  simpa only [mul_div_assoc] using
    prob_exists_restrict_le 2 hI (by simpa using hL) SameDirection
      ((R : ℝ) / ((L.card - 1 : ℕ) : ℝ)) (prob_sameDirection_le L R hL hR)

theorem prob_anyConcurrent_le {I : Type*} [Fintype I]
    (L : Finset (AffineLine F)) (R : ℕ)
    (hI : Nat.card I ≤ Nat.card ↥L) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law I ↥L hI).prob AnyConcurrent ≤
      ((Nat.card I).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := by
  have hevent : (AnyConcurrent : (I ↪ ↥L) → Prop) =
      (fun u => ∃ j : Fin 3 ↪ I, Concurrent (restrict j u)) := by
    funext u
    rfl
  rw [hevent]
  simpa only [mul_div_assoc] using
    prob_exists_restrict_le 3 hI (by simpa using hL) Concurrent
      ((R : ℝ) / ((L.card - 2 : ℕ) : ℝ)) (prob_concurrent_le L R hL hR)

theorem prob_tuple_parallel_le (L : Finset (AffineLine F)) (t R : ℕ)
    (ht : 2 * t ≤ L.card) (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using ht)).prob
        AnyParallel ≤
      ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  simpa only [Nat.card_sum, Nat.card_fin, ← two_mul] using
    prob_anyParallel_le (I := Fin t ⊕ Fin t) L R
      (by simpa [Nat.card_sum, two_mul] using ht) hL hR

theorem prob_tuple_concurrent_le (L : Finset (AffineLine F)) (t R : ℕ)
    (ht : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using ht)).prob
        AnyConcurrent ≤
      ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := by
  simpa only [Nat.card_sum, Nat.card_fin, ← two_mul] using
    prob_anyConcurrent_le (I := Fin t ⊕ Fin t) L R
      (by simpa [Nat.card_sum, two_mul] using ht) hL hR

end RyserCoveringCounterexample.LineCover.LowDegeneracy

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample

theorem exists_subset_card_slot_injective
    {P I J : Type*} [DecidableEq P] [DecidableEq I] [DecidableEq J]
    (left : P → I) (right : P → J) (D h : ℕ) (S : Finset P)
    (hleft : ∀ i, (S.filter fun x => left x = i).card ≤ D)
    (hright : ∀ j, (S.filter fun x => right x = j).card ≤ D)
    (hlarge : 2 * D * h < S.card) :
    ∃ T : Finset P, T ⊆ S ∧ T.card = h ∧
      Set.InjOn left (T : Set P) ∧ Set.InjOn right (T : Set P) := by
  classical
  induction h generalizing S with
  | zero =>
      refine ⟨∅, Finset.empty_subset S, by simp, ?_, ?_⟩
      · simpa only [Finset.coe_empty] using Set.injOn_empty left
      · simpa only [Finset.coe_empty] using Set.injOn_empty right
  | succ h ih =>
      obtain ⟨x, hx⟩ := Finset.card_pos.mp
        (lt_of_le_of_lt (Nat.zero_le _) hlarge)
      let B := (S.filter fun y => left y = left x) ∪
        (S.filter fun y => right y = right x)
      let U := S \ B
      have hUS : U ⊆ S := Finset.sdiff_subset
      have hB : B.card ≤ 2 * D := by
        calc
          B.card ≤ (S.filter fun y => left y = left x).card +
              (S.filter fun y => right y = right x).card :=
            Finset.card_union_le _ _
          _ ≤ D + D := Nat.add_le_add (hleft (left x)) (hright (right x))
          _ = 2 * D := (Nat.two_mul D).symm
      have hUlarge : 2 * D * h < U.card := by
        have hcount : S.card ≤ U.card + B.card :=
          Finset.card_le_card_sdiff_add_card
        have hexpand : 2 * D * h + 2 * D < S.card := by
          simpa only [Nat.mul_succ] using hlarge
        have hsum : 2 * D * h + 2 * D < U.card + 2 * D :=
          hexpand.trans_le (hcount.trans (Nat.add_le_add_left hB U.card))
        exact Nat.add_lt_add_iff_right.mp hsum
      have hUleft : ∀ i, (U.filter fun y => left y = i).card ≤ D := by
        intro i
        exact (Finset.card_le_card
          (Finset.filter_subset_filter (fun y => left y = i) hUS)).trans (hleft i)
      have hUright : ∀ j, (U.filter fun y => right y = j).card ≤ D := by
        intro j
        exact (Finset.card_le_card
          (Finset.filter_subset_filter (fun y => right y = j) hUS)).trans (hright j)
      obtain ⟨T, hTU, hcard, hTL, hTR⟩ := ih U hUleft hUright hUlarge
      have havoid (y : P) (hy : y ∈ T) :
          left y ≠ left x ∧ right y ≠ right x := by
        have hyU := Finset.mem_sdiff.mp (hTU hy)
        constructor
        · intro heq
          exact hyU.2 (Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hyU.1, heq⟩)))
        · intro heq
          exact hyU.2 (Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hyU.1, heq⟩)))
      have hxT : x ∉ T := fun hxT => (havoid x hxT).1 rfl
      refine ⟨insert x T, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hUS (hTU hy)
      · rw [Finset.card_insert_of_notMem hxT, hcard]
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert hxT).2 ⟨hTL, ?_⟩
        rintro ⟨y, hy, heq⟩
        exact (havoid y hy).1 heq
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert hxT).2 ⟨hTR, ?_⟩
        rintro ⟨y, hy, heq⟩
        exact (havoid y hy).2 heq

theorem exists_disjoint_coordinate_sample
    {P I J : Type*} [DecidableEq P] [DecidableEq I] [DecidableEq J]
    (S : Finset P) (left : P → I) (right : P → J) (D h : ℕ)
    (hleft : ∀ i, (S.filter fun x => left x = i).card ≤ D)
    (hright : ∀ j, (S.filter fun x => right x = j).card ≤ D)
    (hlarge : 2 * D * h < S.card) :
    ∃ e : Fin h ↪ ↥S,
      Function.Injective (fun k => left (e k).val) ∧
      Function.Injective (fun k => right (e k).val) := by
  classical
  obtain ⟨T, hTS, hcard, hTL, hTR⟩ :=
    exists_subset_card_slot_injective left right D h S hleft hright hlarge
  let q : Fin h ≃ ↥T := (Finset.equivFinOfCardEq (s := T) hcard).symm
  let e : Fin h ↪ ↥S :=
    { toFun := fun k => ⟨(q k).val, hTS (q k).property⟩
      inj' := by
        intro i j hij
        apply q.injective
        apply Subtype.ext
        exact congrArg (fun x : ↥S => x.val) hij }
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    change left (q i).val = left (q j).val at hij
    exact hTL (q i).property (q j).property hij
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    change right (q i).val = right (q j).val at hij
    exact hTR (q i).property (q j).property hij

end RyserCoveringCounterexample

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def shapePairs (L : Finset (AffineLine F)) (S : Finset (Point F)) :
    Finset (↥L × ↥L) :=
  Finset.univ.filter fun p =>
    p.1 ≠ p.2 ∧ S ≠ linePoints p.1.val ∧ S ≠ linePoints p.2.val ∧
      ∃ x ∈ S, Incidence x p.1.val ∧ Incidence x p.2.val

@[simp] theorem mem_shapePairs (L : Finset (AffineLine F))
    (S : Finset (Point F)) (p : ↥L × ↥L) :
    p ∈ shapePairs L S ↔
      p.1 ≠ p.2 ∧ S ≠ linePoints p.1.val ∧ S ≠ linePoints p.2.val ∧
        ∃ x ∈ S, Incidence x p.1.val ∧ Incidence x p.2.val := by
  simp only [shapePairs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_shapePairs_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R : ℕ} (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    {S : Finset (Point F)} (hS : S ∈ shapes) :
    (shapePairs L S).card ≤ L.card * D * R := by
  classical
  have hfiber (a : ↥L) :
      ((shapePairs L S).filter fun p => p.1 = a).card ≤ D * R := by
    by_cases ha : S = linePoints a.val
    · have hempty : (shapePairs L S).filter (fun p => p.1 = a) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp hpa
        have hne := ((mem_shapePairs L S p).mp hp).2.1
        apply hne
        simpa only [hpa] using ha
      simp only [hempty, Finset.card_empty, Nat.zero_le]
    · let C := S ∩ linePoints a.val
      let pool := C.biUnion fun x => coverPencil L (Sum.inl x)
      calc
        ((shapePairs L S).filter fun p => p.1 = a).card ≤ pool.card := by
          apply Finset.card_le_card_of_injOn (fun p : ↥L × ↥L => p.2.val)
          · intro p hp
            have hpa := (Finset.mem_filter.mp hp).2
            obtain ⟨_, _, _, x, hx, hfirst, hsecond⟩ :=
              (mem_shapePairs L S p).mp (Finset.mem_filter.mp hp).1
            apply Finset.mem_biUnion.mpr
            refine ⟨x, Finset.mem_inter.mpr ⟨hx, ?_⟩, ?_⟩
            · apply (mem_linePoints x a.val).mpr
              simpa only [hpa] using hfirst
            · exact (mem_coverPencil L (Sum.inl x) p.2.val).mpr
                ⟨p.2.property, hsecond⟩
          · intro p hp q hq hpq
            apply Prod.ext
            · exact (Finset.mem_filter.mp hp).2.trans
                (Finset.mem_filter.mp hq).2.symm
            · exact Subtype.ext hpq
        _ ≤ ∑ x ∈ C, (coverPencil L (Sum.inl x)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ C, R := Finset.sum_le_sum fun x _ => hR (Sum.inl x)
        _ = C.card * R := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]
        _ ≤ D * R := Nat.mul_le_mul_right R (hSparse S hS a.val ha)
  calc
    (shapePairs L S).card =
        ∑ a : ↥L, ((shapePairs L S).filter fun p => p.1 = a).card :=
      Finset.card_eq_sum_card_fiberwise
        (s := shapePairs L S) (t := Finset.univ) (f := Prod.fst)
        (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _a : ↥L, D * R := Finset.sum_le_sum fun a _ => hfiber a
    _ = L.card * D * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Nat.nsmul_eq_mul, Nat.mul_assoc]

theorem shape_ne_linePoints_of_not_mem_tupleShapes
    {t : ℕ} (a : LineTuple F t) {S : Finset (Point F)}
    (hS : S ∉ tupleShapes a) (slot : Fin t ⊕ Fin t) :
    S ≠ linePoints (a slot) := by
  intro heq
  exact hS ((mem_tupleShapes a S).mpr ⟨slot, heq.symm⟩)

theorem exists_disjoint_shapePairs_of_occupancy
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D h t : ℕ} (hSparse : SparseShapes shapes D)
    {S : Finset (Point F)} (hS : S ∈ shapes) (u : CoverSample L t)
    (hnot : S ∉ tupleShapes (liftSample L u))
    (hlarge : 2 * D * h < (S ∩ crossPoints (liftSample L u)).card) :
    ∃ left right : Fin h ↪ Fin t, ∀ k,
      (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ shapePairs L S := by
  classical
  let a := liftSample L u
  let C := S ∩ crossPoints a
  have hrepr (x : ↥C) : ∃ i j : Fin t,
      Incidence x.val (a (Sum.inl i)) ∧ Incidence x.val (a (Sum.inr j)) :=
    (mem_crossPoints a x.val).mp (Finset.mem_inter.mp x.property).2
  let left : ↥C → Fin t := fun x => Classical.choose (hrepr x)
  let right : ↥C → Fin t :=
    fun x => Classical.choose (Classical.choose_spec (hrepr x))
  have hinc (x : ↥C) :
      Incidence x.val (a (Sum.inl (left x))) ∧
        Incidence x.val (a (Sum.inr (right x))) :=
    Classical.choose_spec (Classical.choose_spec (hrepr x))
  have hne (slot : Fin t ⊕ Fin t) : S ≠ linePoints (a slot) :=
    shape_ne_linePoints_of_not_mem_tupleShapes a hnot slot
  have hfiber (coord : ↥C → Fin t) (side : Fin t → Fin t ⊕ Fin t)
      (hcoord : ∀ x : ↥C, Incidence x.val (a (side (coord x)))) (i : Fin t) :
      ((Finset.univ : Finset ↥C).filter fun x => coord x = i).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (a (side i))).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥C => x.val)
        · intro x hx
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (a (side i))).mpr
          simpa only [(Finset.mem_filter.mp hx).2] using hcoord x
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hSparse S hS (a (side i)) (hne (side i))
  have hlarge' : 2 * D * h < (Finset.univ : Finset ↥C).card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hlarge
  obtain ⟨e, hleft, hright⟩ := exists_disjoint_coordinate_sample
    (Finset.univ : Finset ↥C) left right D h
    (hfiber left Sum.inl (fun x => (hinc x).1))
    (hfiber right Sum.inr (fun x => (hinc x).2)) hlarge'
  let i : Fin h ↪ Fin t := ⟨fun k => left (e k).val, hleft⟩
  let j : Fin h ↪ Fin t := ⟨fun k => right (e k).val, hright⟩
  refine ⟨i, j, ?_⟩
  intro k
  let x : ↥C := (e k).val
  apply (mem_shapePairs L S _).mpr
  refine ⟨?_, hne (Sum.inl (i k)), hne (Sum.inr (j k)),
    x.val, (Finset.mem_inter.mp x.property).1, (hinc x).1, (hinc x).2⟩
  intro heq
  have hslots := u.injective heq
  cases hslots

theorem prob_shape_occupancy_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R h t : ℕ} [Nonempty (CoverSample L t)]
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    {S : Finset (Point F)} (hS : S ∈ shapes) :
    (FiniteLaw.uniform (CoverSample L t)).prob (fun u =>
      S ∉ tupleShapes (liftSample L u) ∧
        2 * D * h < (S ∩ crossPoints (liftSample L u)).card) ≤
      (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform (CoverSample L t)
  have hcard : ((shapePairs L S).card : ℝ) ≤ ((L.card * D * R : ℕ) : ℝ) :=
    Nat.cast_le.mpr (card_shapePairs_le shapes L hSparse hR hS)
  calc
    _ ≤ μ.prob (fun u => ∃ left right : Fin h ↪ Fin t, ∀ k,
        (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ shapePairs L S) := by
      apply μ.prob_mono
      intro u hu
      exact exists_disjoint_shapePairs_of_occupancy shapes L hSparse hS u hu.1 hu.2
    _ ≤ (t : ℝ) ^ (2 * h) * ((shapePairs L S).card : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
      simpa only [Fintype.card_coe] using
        (InjectionSampling.prob_exists_disjoint_pairs_le
          (h := h) (t := t) (shapePairs L S))
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard h)
        (pow_nonneg (Nat.cast_nonneg _) (2 * h))

theorem prob_bad_occupancy_le
    (shapes : Finset (Finset (Point F))) (L : Finset (AffineLine F))
    {D R h t : ℕ} [Nonempty (CoverSample L t)]
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob (fun u =>
      ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
        2 * D * h < (S ∩ crossPoints (liftSample L u)).card) ≤
      (shapes.card : ℝ) * (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
        (L.card.descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform (CoverSample L t)
  calc
    _ = μ.prob (fun u => ∃ S : ↥shapes,
        S.val ∉ tupleShapes (liftSample L u) ∧
          2 * D * h < (S.val ∩ crossPoints (liftSample L u)).card) := by
      congr 1
      funext u
      apply propext
      constructor
      · rintro ⟨S, hS, hbad⟩
        exact ⟨⟨S, hS⟩, hbad⟩
      · rintro ⟨S, hbad⟩
        exact ⟨S.val, S.property, hbad⟩
    _ ≤ ∑ S : ↥shapes, μ.prob (fun u =>
        S.val ∉ tupleShapes (liftSample L u) ∧
          2 * D * h < (S.val ∩ crossPoints (liftSample L u)).card) :=
      μ.prob_exists_le _
    _ ≤ ∑ _S : ↥shapes,
        (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
          (L.card.descFactorial (2 * h) : ℝ) := by
      apply Finset.sum_le_sum
      intro S _
      exact prob_shape_occupancy_le shapes L hSparse hR S.property
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] {t : ℕ}

def NoParallel (a : LineTuple F t) : Prop :=
  ∀ i j, i ≠ j → (a i).1 ≠ (a j).1

def NoConcurrentTriple (a : LineTuple F t) : Prop :=
  ∀ p : ProjectivePoint F, ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ProjectiveIncidence p (some (a i)) →
    ProjectiveIncidence p (some (a j)) →
    ProjectiveIncidence p (some (a k)) → False

theorem finiteCrossings_of_no_parallel (a : LineTuple F t) (h : NoParallel a) :
    FiniteCrossings a := let _ := instFintypeF; let _ := instDecidableEqF; by
  intro i j
  exact (existsUnique_incident_of_ne_direction (a (Sum.inl i)) (a (Sum.inr j))
    (h _ _ (by intro he; cases he))).exists

theorem crossPoints_eq_image_grid (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2))) :
    crossPoints a = Finset.univ.image g := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, hi, hj⟩ := (mem_crossPoints a x).mp hx
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    exact eq_of_common_incidence_of_ne_lines (left_ne_right a i j)
      (hg (i, j)).1 (hg (i, j)).2 hi hj
  · intro hx
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_crossPoints a (g ij)).mpr ⟨ij.1, ij.2, (hg ij).1, (hg ij).2⟩

theorem crossPoints_card_of_grid (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2)))
    (hinj : Function.Injective g) : (crossPoints a).card = t * t := by
  rw [crossPoints_eq_image_grid a g hg, Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

theorem grid_injective_of_no_concurrentTriple (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2)))
    (h : NoConcurrentTriple a) : Function.Injective g := let _ := instFintypeF; let _ := instDecidableEqF; by
  rintro ⟨i, j⟩ ⟨k, l⟩ he
  have hleft : Incidence (g (i, j)) (a (Sum.inl k)) := by
    rw [he]
    exact (hg (k, l)).1
  have hright : Incidence (g (i, j)) (a (Sum.inr l)) := by
    rw [he]
    exact (hg (k, l)).2
  have hik : i = k := by
    by_contra hik
    exact h (Sum.inl (g (i, j))) (Sum.inl i) (Sum.inl k) (Sum.inr j)
      (fun hi => hik (Sum.inl.inj hi))
      (by intro hi; cases hi) (by intro hi; cases hi)
      (hg (i, j)).1 hleft (hg (i, j)).2
  have hjl : j = l := by
    by_contra hjl
    exact h (Sum.inl (g (i, j))) (Sum.inl i) (Sum.inr j) (Sum.inr l)
      (by intro hi; cases hi) (by intro hi; cases hi)
      (fun hi => hjl (Sum.inr.inj hi))
      (hg (i, j)).1 (hg (i, j)).2 hright
  exact Prod.ext hik hjl

theorem finiteCrossings_card_of_no_parallel_no_concurrentTriple
    (a : LineTuple F t) (hp : NoParallel a) (hc : NoConcurrentTriple a) :
    FiniteCrossings a ∧ (crossPoints a).card = t * t := by
  have hfinite := finiteCrossings_of_no_parallel a hp
  choose g hg using hfinite
  let grid : Fin t × Fin t → Point F := fun ij => g ij.1 ij.2
  have hgrid : ∀ ij, Incidence (grid ij) (a (Sum.inl ij.1)) ∧
      Incidence (grid ij) (a (Sum.inr ij.2)) := fun ij => hg ij.1 ij.2
  exact ⟨finiteCrossings_of_no_parallel a hp, crossPoints_card_of_grid a grid hgrid
    (grid_injective_of_no_concurrentTriple a grid hgrid hc)⟩

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def lowFailureBound (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ) : ℝ :=
  2 * (orderedPairMass Incidence X L : ℝ) /
      (δ * (L.card.descFactorial 2 : ℝ)) +
    ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) +
    ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) +
    (shapes.card : ℝ) * (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
      (L.card.descFactorial (2 * h) : ℝ)

def LowBad (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (u : CoverSample L t) : Prop :=
  δ * (t : ℝ) ^ 2 / 2 ≤ ((X ∩ crossPoints (liftSample L u)).card : ℝ) ∨
    LowDegeneracy.AnyParallel u ∨ LowDegeneracy.AnyConcurrent u ∨
    ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
      2 * D * h < (S ∩ crossPoints (liftSample L u)).card

theorem direction_card_le_of_coverPencil
    (L : Finset (AffineLine F)) {R : ℕ}
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    (d : Direction F) : (L.filter fun l => l.1 = d).card ≤ R := let _ := instFintypeF; by
  simpa only [coverPencil, ProjectiveIncidence, eq_comm] using hR (Sum.inr d)

private theorem prob_four_union_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (P Q R S : Ω → Prop) :
    μ.prob (fun u => P u ∨ Q u ∨ R u ∨ S u) ≤
      μ.prob P + μ.prob Q + μ.prob R + μ.prob S := by
  calc
    _ ≤ μ.prob P + μ.prob (fun u => Q u ∨ R u ∨ S u) :=
      μ.prob_union_le _ _
    _ ≤ μ.prob P + (μ.prob Q + μ.prob (fun u => R u ∨ S u)) :=
      add_le_add (le_refl (μ.prob P)) (μ.prob_union_le Q (fun u => R u ∨ S u))
    _ ≤ μ.prob P + (μ.prob Q + (μ.prob R + μ.prob S)) :=
      add_le_add (le_refl (μ.prob P))
        (add_le_add (le_refl (μ.prob Q)) (μ.prob_union_le R S))
    _ = _ := by simp only [add_assoc]

private theorem prob_uniform_parallel_le (L : Finset (AffineLine F)) (t R : ℕ)
    [Nonempty (CoverSample L t)] (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob LowDegeneracy.AnyParallel ≤
      ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  have hbound := LowDegeneracy.prob_tuple_parallel_le L t R hsize
    ((by decide : 2 ≤ 3).trans hL) (direction_card_le_of_coverPencil L hR)
  rw [InjectionSampling.law_eq_uniform] at hbound
  exact hbound

private theorem prob_uniform_concurrent_le (L : Finset (AffineLine F)) (t R : ℕ)
    [Nonempty (CoverSample L t)] (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob LowDegeneracy.AnyConcurrent ≤
      ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := let _ := instFintypeF; by
  have hbound := LowDegeneracy.prob_tuple_concurrent_le L t R hsize hL hR
  rw [InjectionSampling.law_eq_uniform] at hbound
  exact hbound

theorem prob_lowBad_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ)
    [Nonempty (CoverSample L t)]
    (hδ : 0 < δ) (ht : 0 < t) (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob (LowBad X L shapes D h t δ) ≤
      lowFailureBound X L shapes D R h t δ := by
  unfold LowBad lowFailureBound
  apply (prob_four_union_le (FiniteLaw.uniform (CoverSample L t)) _ _ _ _).trans
  exact add_le_add
    (add_le_add
      (add_le_add (prob_many_cross_survivors_le X L hδ ht)
        (prob_uniform_parallel_le L t R hsize hL hR))
      (prob_uniform_concurrent_le L t R hsize hL hR))
    (prob_bad_occupancy_le (h := h) (t := t) shapes L hSparse hR)

theorem admissible_of_not_lowBad
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (u : CoverSample L t) (hu : ¬ LowBad X L shapes D h t δ u) :
    AdmissibleTuple shapes D h (liftSample L u) ∧
      ((X ∩ crossPoints (liftSample L u)).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  have hmany : ¬ δ * (t : ℝ) ^ 2 / 2 ≤
      ((X ∩ crossPoints (liftSample L u)).card : ℝ) :=
    fun he => hu (Or.inl he)
  have hparallel : ¬ LowDegeneracy.AnyParallel u :=
    fun he => hu (Or.inr (Or.inl he))
  have hconcurrent : ¬ LowDegeneracy.AnyConcurrent u :=
    fun he => hu (Or.inr (Or.inr (Or.inl he)))
  have hoccupied : ¬ ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
      2 * D * h < (S ∩ crossPoints (liftSample L u)).card :=
    fun he => hu (Or.inr (Or.inr (Or.inr he)))
  have hp : NoParallel (liftSample L u) := by
    intro i j hij hdir
    exact hparallel ((LowDegeneracy.anyParallel_iff u).mpr ⟨i, j, hij, hdir⟩)
  have hc : NoConcurrentTriple (liftSample L u) := by
    intro p i j k hij hik hjk hi hj hk
    exact hconcurrent ((LowDegeneracy.anyConcurrent_iff u).mpr
      ⟨i, j, k, hij, hik, hjk, p, hi, hj, hk⟩)
  obtain ⟨hfinite, hcard⟩ :=
    finiteCrossings_card_of_no_parallel_no_concurrentTriple (liftSample L u) hp hc
  refine ⟨⟨hfinite, hcard, ?_⟩, lt_of_not_ge hmany⟩
  intro S hS hnot
  exact Nat.le_of_not_gt (fun hlarge => hoccupied ⟨S, hS, hnot, hlarge⟩)

theorem exists_low_sample_of_failureBound_lt_one
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (ht : 0 < t) (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    (hbudget : lowFailureBound X L shapes D R h t δ < 1) :
    ∃ a : LineTuple F t, (∀ i, a i ∈ L) ∧ AdmissibleTuple shapes D h a ∧
      ((X ∩ crossPoints a).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  classical
  let : Nonempty (CoverSample L t) := InjectionSampling.sample_nonempty
    (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using hsize)
  let μ := FiniteLaw.uniform (CoverSample L t)
  have hprob := prob_lowBad_le X L shapes D R h t δ hδ ht hsize hL hSparse hR
  have hex : ∃ u : CoverSample L t, ¬ LowBad X L shapes D h t δ u := by
    by_contra hnone
    have hall (u : CoverSample L t) : LowBad X L shapes D h t δ u := by
      by_contra hu
      exact hnone ⟨u, hu⟩
    have hone : 1 ≤ μ.prob (LowBad X L shapes D h t δ) := by
      simpa only [FiniteLaw.prob_true] using
        (μ.prob_mono (P := fun _ => True) (Q := LowBad X L shapes D h t δ)
          (fun u _ => hall u))
    exact (not_le_of_gt (hprob.trans_lt hbudget)) hone
  obtain ⟨u, hu⟩ := hex
  exact ⟨liftSample L u, liftSample_mem L u,
    admissible_of_not_lowBad X L shapes D h t δ u hu⟩

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

abbrev PencilPopulation (L : Finset (AffineLine F)) (p : ProjectivePoint F) :=
  ↥(coverPencil L p)

abbrev ComplementPopulation (L : Finset (AffineLine F)) (p : ProjectivePoint F) :=
  ↥(L \ coverPencil L p)

abbrev HighSample (L : Finset (AffineLine F)) (p : ProjectivePoint F) (t : ℕ) :=
  (Fin t ↪ PencilPopulation L p) × (Fin t ↪ ComplementPopulation L p)

theorem pencilPopulation_incident (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (k : PencilPopulation L p) : ProjectiveIncidence p (some k.val) :=
  (mem_coverPencil L p k.val).mp k.property |>.2

theorem complementPopulation_mem (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (c : ComplementPopulation L p) : c.val ∈ L := let _ := instFintypeF;
  (Finset.mem_sdiff.mp c.property).1

theorem complementPopulation_not_incident (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (c : ComplementPopulation L p) :
    ¬ ProjectiveIncidence p (some c.val) := by
  intro hc
  exact (Finset.mem_sdiff.mp c.property).2
    ((mem_coverPencil L p c.val).mpr ⟨complementPopulation_mem L p c, hc⟩)

theorem pencil_ne_complement (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (k : PencilPopulation L p) (c : ComplementPopulation L p) : k.val ≠ c.val := by
  intro h
  apply complementPopulation_not_incident L p c
  rw [← h]
  exact pencilPopulation_incident L p k

def highTuple (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (s : HighSample L p t) : LineTuple F t where
  toFun := Sum.elim (fun i => (s.1 i).val) (fun j => (s.2 j).val)
  inj' := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (s.1.injective (Subtype.ext hab))
      | inr j => exact (pencil_ne_complement L p (s.1 i) (s.2 j) hab).elim
    | inr i =>
      cases b with
      | inl j => exact (pencil_ne_complement L p (s.1 j) (s.2 i) hab.symm).elim
      | inr j => exact congrArg Sum.inr (s.2.injective (Subtype.ext hab))

@[simp] theorem highTuple_left (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t) :
    highTuple L p s (Sum.inl i) = (s.1 i).val := rfl

@[simp] theorem highTuple_right (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t) :
    highTuple L p s (Sum.inr i) = (s.2 i).val := rfl

theorem highTuple_mem (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t ⊕ Fin t) : highTuple L p s i ∈ L := by
  cases i with
  | inl i => exact coverPencil_subset L p (s.1 i).property
  | inr i => exact complementPopulation_mem L p (s.2 i)

def highCrossPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : Finset (PencilPopulation L p × ComplementPopulation L p) :=
  Finset.univ.filter fun kc =>
    ∃ x ∈ X, Incidence x kc.1.val ∧ Incidence x kc.2.val

@[simp] theorem mem_highCrossPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (kc : PencilPopulation L p × ComplementPopulation L p) :
    kc ∈ highCrossPairs X L p ↔
      ∃ x ∈ X, Incidence x kc.1.val ∧ Incidence x kc.2.val := let _ := instFintypeF; by
  simp only [highCrossPairs, Finset.mem_filter, Finset.mem_univ, true_and]

def highShapePairs (S : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : Finset (PencilPopulation L p × ComplementPopulation L p) :=
  (highCrossPairs S L p).filter fun kc =>
    S ≠ linePoints kc.1.val ∧ S ≠ linePoints kc.2.val

@[simp] theorem mem_highShapePairs (S : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (kc : PencilPopulation L p × ComplementPopulation L p) :
    kc ∈ highShapePairs S L p ↔
      (∃ x ∈ S, Incidence x kc.1.val ∧ Incidence x kc.2.val) ∧
      S ≠ linePoints kc.1.val ∧ S ≠ linePoints kc.2.val := by
  simp only [highShapePairs, Finset.mem_filter, mem_highCrossPairs]

def highSurvivorPairCount (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (s : HighSample L p t) : ℕ :=
  (Finset.univ.filter fun ij : Fin t × Fin t =>
    (s.1 ij.1, s.2 ij.2) ∈ highCrossPairs X L p).card

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem pencil_eq_at_complement
    (x : Point F) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (c : ComplementPopulation L p) (k l : PencilPopulation L p)
    (hxc : Incidence x c.val) (hxk : Incidence x k.val) (hxl : Incidence x l.val) :
    k = l := by
  apply Subtype.ext
  exact eq_affineLine_of_common_projective_incidence
    (ne_of_projectiveIncidence_of_not_projectiveIncidence
      ((projectiveIncidence_finite_affine x c.val).mpr hxc)
      (complementPopulation_not_incident L p c))
    ((projectiveIncidence_finite_affine x k.val).mpr hxk)
    (pencilPopulation_incident L p k)
    ((projectiveIncidence_finite_affine x l.val).mpr hxl)
    (pencilPopulation_incident L p l)

private theorem pointCrossPairs_card_le
    (x : Point F) (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
      Incidence x kc.1.val ∧ Incidence x kc.2.val).card ≤
      multiplicity Incidence L x - 1 := by
  let B := Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
    Incidence x kc.1.val ∧ Incidence x kc.2.val
  change B.card ≤ multiplicity Incidence L x - 1
  by_cases hB : B.Nonempty
  · obtain ⟨kc, hkc⟩ := hB
    have hxkc := (Finset.mem_filter.mp hkc).2
    let C := (L.filter (Incidence x)).erase kc.1.val
    have hk : kc.1.val ∈ L.filter (Incidence x) :=
      Finset.mem_filter.mpr ⟨coverPencil_subset L p kc.1.property, hxkc.1⟩
    let f : ↥B → ↥C := fun q =>
      ⟨q.val.2.val, Finset.mem_erase.mpr
        ⟨(pencil_ne_complement L p kc.1 q.val.2).symm,
          Finset.mem_filter.mpr ⟨complementPopulation_mem L p q.val.2,
            (Finset.mem_filter.mp q.property).2.2⟩⟩⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Prod.ext
      · exact pencil_eq_at_complement x L p a.val.2 a.val.1 b.val.1
          (Finset.mem_filter.mp a.property).2.2
          (Finset.mem_filter.mp a.property).2.1
          (Finset.mem_filter.mp b.property).2.1
      · exact Subtype.ext (congrArg (fun z : ↥C => z.val) hab)
    calc
      B.card ≤ C.card := Finset.card_le_card_of_injective hf
      _ = multiplicity Incidence L x - 1 := by
        have hfilter :
            @Finset.filter _ (Incidence x)
              (fun l => Classical.propDecidable (Incidence x l)) L =
                L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
        unfold multiplicity
        rw [hfilter]
        exact Finset.card_erase_of_mem hk
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB, Finset.card_empty]
    exact Nat.zero_le _

theorem highCrossPairs_card_le
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (highCrossPairs X L p).card ≤ overlapExcess Incidence X L := by
  let B (x : Point F) :=
    Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
      Incidence x kc.1.val ∧ Incidence x kc.2.val
  have hcover : highCrossPairs X L p = X.biUnion B := by
    ext kc
    simp only [mem_highCrossPairs, Finset.mem_biUnion, B,
      Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    (highCrossPairs X L p).card = (X.biUnion B).card := congrArg Finset.card hcover
    _ ≤ ∑ x ∈ X, (B x).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ X, (multiplicity Incidence L x - 1) :=
      Finset.sum_le_sum fun x _ => pointCrossPairs_card_le x L p
    _ = overlapExcess Incidence X L := rfl

theorem highShapePairs_card_le
    (S : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F) (D : ℕ)
    (hsparse : ∀ l, S ≠ linePoints l → (S ∩ linePoints l).card ≤ D) :
    (highShapePairs S L p).card ≤ D * (L \ coverPencil L p).card := by
  let B := highShapePairs S L p
  have hfiber (c : ComplementPopulation L p) :
      (B.filter fun kc => kc.2 = c).card ≤ D := by
    by_cases heq : S = linePoints c.val
    · have hempty : (B.filter fun kc => kc.2 = c) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨kc, hkc⟩
        have hm := (mem_highShapePairs S L p kc).mp (Finset.mem_filter.mp hkc).1
        have hc : kc.2 = c := (Finset.mem_filter.mp hkc).2
        exact hm.2.2 (heq.trans
          (congrArg (fun a : ComplementPopulation L p => linePoints a.val) hc.symm))
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · let T := B.filter fun kc => kc.2 = c
      let xof (q : ↥T) : Point F :=
        Classical.choose ((mem_highShapePairs S L p q.val).mp
          (Finset.mem_filter.mp q.property).1).1
      have hxof (q : ↥T) : xof q ∈ S ∧
          Incidence (xof q) q.val.1.val ∧ Incidence (xof q) q.val.2.val :=
        Classical.choose_spec ((mem_highShapePairs S L p q.val).mp
          (Finset.mem_filter.mp q.property).1).1
      have hxc (q : ↥T) : Incidence (xof q) c.val := by
        have hq := (hxof q).2.2
        rw [(Finset.mem_filter.mp q.property).2] at hq
        exact hq
      let f : ↥T → ↥(S ∩ linePoints c.val) := fun q =>
        ⟨xof q, Finset.mem_inter.mpr
          ⟨(hxof q).1, (mem_linePoints (xof q) c.val).mpr (hxc q)⟩⟩
      have hf : Function.Injective f := by
        intro a b hab
        have hxy : xof a = xof b :=
          congrArg (fun z : ↥(S ∩ linePoints c.val) => z.val) hab
        apply Subtype.ext
        apply Prod.ext
        · apply pencil_eq_at_complement (xof a) L p c a.val.1 b.val.1
          · exact hxc a
          · exact (hxof a).2.1
          · rw [hxy]
            exact (hxof b).2.1
        · exact (Finset.mem_filter.mp a.property).2.trans
            (Finset.mem_filter.mp b.property).2.symm
      exact (Finset.card_le_card_of_injective hf).trans (hsparse c.val heq)
  have hsplit : B.card = ∑ c : ComplementPopulation L p,
      (B.filter fun kc => kc.2 = c).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  calc
    (highShapePairs S L p).card = ∑ c : ComplementPopulation L p,
        (B.filter fun kc => kc.2 = c).card := hsplit
    _ ≤ ∑ _c : ComplementPopulation L p, D := Finset.sum_le_sum fun c _ => hfiber c
    _ = D * (L \ coverPencil L p).card := by simp [ComplementPopulation, Nat.mul_comm]

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def highParallelLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  Finset.univ.biUnion fun j => Finset.univ.filter fun k => k.val.1 = (b j).val.1

def highCollisionLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  Finset.univ.biUnion fun ij : Fin t × Fin t => Finset.univ.filter fun k =>
    ij.1 ≠ ij.2 ∧ ∃ x : ProjectivePoint F,
      ProjectiveIncidence x (some k.val) ∧
      ProjectiveIncidence x (some (b ij.1).val) ∧
      ProjectiveIncidence x (some (b ij.2).val)

def highBadLines (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (b : Fin t ↪ ComplementPopulation L p) : Finset (PencilPopulation L p) :=
  highParallelLines L p b ∪ highCollisionLines L p b

@[simp] theorem mem_highParallelLines (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p)
    (k : PencilPopulation L p) :
    k ∈ highParallelLines L p b ↔ ∃ j, k.val.1 = (b j).val.1 := let _ := instFintypeF; by
  simp only [highParallelLines, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_filter, true_and]

@[simp] theorem mem_highCollisionLines (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p)
    (k : PencilPopulation L p) :
    k ∈ highCollisionLines L p b ↔ ∃ i j, i ≠ j ∧
      ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
        ProjectiveIncidence x (some (b i).val) ∧
        ProjectiveIncidence x (some (b j).val) := by
  simp only [highCollisionLines, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_filter, true_and, Prod.exists]

theorem highParallelLines_card_le (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highParallelLines L p b).card ≤ t := by
  have hone (j : Fin t) :
      (Finset.univ.filter fun k : PencilPopulation L p => k.val.1 = (b j).val.1).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    have hd := (Finset.mem_filter.mp hk).2
    have hd' := (Finset.mem_filter.mp hk').2
    cases p with
    | inl x =>
      apply Subtype.ext
      exact line_eq_of_direction_eq_of_incidence (hd.trans hd'.symm)
        (pencilPopulation_incident L (Sum.inl x) k)
        (pencilPopulation_incident L (Sum.inl x) k')
    | inr d =>
      have hkdir : d = k.val.1 := pencilPopulation_incident L (Sum.inr d) k
      exact (complementPopulation_not_incident L (Sum.inr d) (b j)
        (hkdir.trans hd)).elim
  calc
    _ ≤ ∑ j : Fin t,
        (Finset.univ.filter fun k : PencilPopulation L p => k.val.1 = (b j).val.1).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin t, 1 := Finset.sum_le_sum (fun j _ => hone j)
    _ = t := by simp

theorem highCollisionLines_card_le (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highCollisionLines L p b).card ≤ t * t := by
  have hone (ij : Fin t × Fin t) :
      (Finset.univ.filter fun k : PencilPopulation L p => ij.1 ≠ ij.2 ∧
        ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
          ProjectiveIncidence x (some (b ij.1).val) ∧
          ProjectiveIncidence x (some (b ij.2).val)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    obtain ⟨hij, x, hxk, hxc, hxc'⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨_, y, hyk, hyc, hyc'⟩ := (Finset.mem_filter.mp hk').2
    have hlines : (b ij.1).val ≠ (b ij.2).val := by
      intro he
      exact hij (b.injective (Subtype.ext he))
    have hxy : x = y := eq_projectivePoint_of_common_incidence
      (fun he => hlines (Option.some.inj he)) hxc hxc' hyc hyc'
    subst y
    have hxp : x ≠ p := ne_of_projectiveIncidence_of_not_projectiveIncidence
      hxc (complementPopulation_not_incident L p (b ij.1))
    apply Subtype.ext
    exact eq_affineLine_of_common_projective_incidence hxp.symm
      (pencilPopulation_incident L p k) hxk
      (pencilPopulation_incident L p k') hyk
  calc
    _ ≤ ∑ ij : Fin t × Fin t,
        (Finset.univ.filter fun k : PencilPopulation L p => ij.1 ≠ ij.2 ∧
          ∃ x : ProjectivePoint F, ProjectiveIncidence x (some k.val) ∧
            ProjectiveIncidence x (some (b ij.1).val) ∧
            ProjectiveIncidence x (some (b ij.2).val)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ij : Fin t × Fin t, 1 := Finset.sum_le_sum (fun ij _ => hone ij)
    _ = t * t := by simp

theorem highBadLines_card_le (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (b : Fin t ↪ ComplementPopulation L p) :
    (highBadLines L p b).card ≤ t + t * t :=
  (Finset.card_union_le (highParallelLines L p b) (highCollisionLines L p b)).trans (Nat.add_le_add
    (highParallelLines_card_le L p b) (highCollisionLines_card_le L p b))

theorem highTuple_grid_of_avoids (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t)
    (havoid : ∀ i, s.1 i ∉ highBadLines L p s.2) :
    FiniteCrossings (highTuple L p s) ∧ (crossPoints (highTuple L p s)).card = t * t := by
  have hfinite (i j : Fin t) :
      ∃ x, Incidence x (s.1 i).val ∧ Incidence x (s.2 j).val := by
    have hdir : (s.1 i).val.1 ≠ (s.2 j).val.1 := by
      intro he
      apply havoid i
      exact Finset.mem_union_left _
        ((mem_highParallelLines L p s.2 (s.1 i)).mpr ⟨j, he⟩)
    exact (existsUnique_incident_of_ne_direction _ _ hdir).exists
  let f : Fin t × Fin t → Point F := fun ij => Classical.choose (hfinite ij.1 ij.2)
  have hf (ij : Fin t × Fin t) :
      Incidence (f ij) (s.1 ij.1).val ∧ Incidence (f ij) (s.2 ij.2).val :=
    Classical.choose_spec (hfinite ij.1 ij.2)
  have hinj : Function.Injective f := by
    intro ij kl he
    have hkl := hf kl
    rw [← he] at hkl
    have hxp : (Sum.inl (f ij) : ProjectivePoint F) ≠ p :=
      ne_of_projectiveIncidence_of_not_projectiveIncidence
        (l := some (s.2 ij.2).val)
        (hf ij).2 (complementPopulation_not_incident L p (s.2 ij.2))
    have hfirst : ij.1 = kl.1 := by
      apply s.1.injective
      apply Subtype.ext
      exact eq_affineLine_of_common_projective_incidence hxp.symm
        (pencilPopulation_incident L p (s.1 ij.1)) (hf ij).1
        (pencilPopulation_incident L p (s.1 kl.1)) hkl.1
    have hsecond : ij.2 = kl.2 := by
      by_contra hne
      apply havoid ij.1
      apply Finset.mem_union_right
      apply (mem_highCollisionLines L p s.2 (s.1 ij.1)).mpr
      exact ⟨ij.2, kl.2, hne, Sum.inl (f ij), (hf ij).1, (hf ij).2, hkl.2⟩
    exact Prod.ext hfirst hsecond
  have hset : crossPoints (highTuple L p s) = Finset.univ.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, j, hi, hj⟩ := (mem_crossPoints (highTuple L p s) x).mp hx
      have he : f (i, j) = x := eq_of_common_incidence_of_ne_lines
        (pencil_ne_complement L p (s.1 i) (s.2 j))
        (hf (i, j)).1 (hf (i, j)).2 hi hj
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, he⟩
    · intro hx
      obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_crossPoints (highTuple L p s) (f ij)).mpr
        ⟨ij.1, ij.2, (hf ij).1, (hf ij).2⟩
  refine ⟨hfinite, ?_⟩
  rw [hset, Finset.card_image_of_injective _ hinj]
  simp

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem highShapePairs_matching_of_large
    (S : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (D h : ℕ) {t : ℕ} (s : HighSample L p t)
    (hsparse : ∀ l : AffineLine F, S ≠ linePoints l → (S ∩ linePoints l).card ≤ D)
    (hnot : S ∉ tupleShapes (highTuple L p s))
    (hlarge : 2 * D * h < (S ∩ crossPoints (highTuple L p s)).card) :
    ∃ i j : Fin h ↪ Fin t, ∀ k,
      (s.1 (i k), s.2 (j k)) ∈ highShapePairs S L p := by
  let P := S ∩ crossPoints (highTuple L p s)
  have hex (x : ↥P) : ∃ ij : Fin t × Fin t,
      Incidence x.val (s.1 ij.1).val ∧ Incidence x.val (s.2 ij.2).val := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints (highTuple L p s) x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep : ↥P → Fin t × Fin t := fun x => Classical.choose (hex x)
  have hrep (x : ↥P) :
      Incidence x.val (s.1 (rep x).1).val ∧ Incidence x.val (s.2 (rep x).2).val :=
    Classical.choose_spec (hex x)
  have hnotleft (i : Fin t) : S ≠ linePoints (s.1 i).val := by
    intro he
    exact hnot ((mem_tupleShapes (highTuple L p s) S).mpr ⟨Sum.inl i, he.symm⟩)
  have hnotright (j : Fin t) : S ≠ linePoints (s.2 j).val := by
    intro he
    exact hnot ((mem_tupleShapes (highTuple L p s) S).mpr ⟨Sum.inr j, he.symm⟩)
  have hleft (i : Fin t) :
      (Finset.univ.filter fun x : ↥P => (rep x).1 = i).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (s.1 i).val).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥P => x.val)
        · intro x hx
          have hxi := (Finset.mem_filter.mp hx).2
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (s.1 i).val).mpr
          simpa only [hxi] using (hrep x).1
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hsparse _ (hnotleft i)
  have hright (j : Fin t) :
      (Finset.univ.filter fun x : ↥P => (rep x).2 = j).card ≤ D := by
    calc
      _ ≤ (S ∩ linePoints (s.2 j).val).card := by
        apply Finset.card_le_card_of_injOn (fun x : ↥P => x.val)
        · intro x hx
          have hxj := (Finset.mem_filter.mp hx).2
          refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1, ?_⟩
          apply (mem_linePoints x.val (s.2 j).val).mpr
          simpa only [hxj] using (hrep x).2
        · intro x _ y _ hxy
          exact Subtype.ext hxy
      _ ≤ D := hsparse _ (hnotright j)
  obtain ⟨e, hei, hej⟩ := exists_disjoint_coordinate_sample
    (Finset.univ : Finset ↥P) (fun x => (rep x).1) (fun x => (rep x).2)
    D h hleft hright (by simpa only [Finset.card_univ, Fintype.card_coe] using hlarge)
  let i : Fin h ↪ Fin t := ⟨fun k => (rep (e k).val).1, hei⟩
  let j : Fin h ↪ Fin t := ⟨fun k => (rep (e k).val).2, hej⟩
  refine ⟨i, j, ?_⟩
  intro k
  apply (mem_highShapePairs S L p (s.1 (i k), s.2 (j k))).mpr
  refine ⟨?_, hnotleft (i k), hnotright (j k)⟩
  exact ⟨(e k).val.val, (Finset.mem_inter.mp (e k).val.property).1,
    (hrep (e k).val).1, (hrep (e k).val).2⟩

theorem highSurvivorPoints_card_le
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) :
    (X ∩ crossPoints (highTuple L p s)).card ≤ highSurvivorPairCount X L p s := by
  let P := X ∩ crossPoints (highTuple L p s)
  let Q := Finset.univ.filter fun ij : Fin t × Fin t =>
    (s.1 ij.1, s.2 ij.2) ∈ highCrossPairs X L p
  have hex (x : ↥P) : ∃ ij : Fin t × Fin t,
      Incidence x.val (s.1 ij.1).val ∧ Incidence x.val (s.2 ij.2).val := by
    obtain ⟨i, j, hi, hj⟩ :=
      (mem_crossPoints (highTuple L p s) x.val).mp (Finset.mem_inter.mp x.property).2
    exact ⟨(i, j), hi, hj⟩
  let rep : ↥P → Fin t × Fin t := fun x => Classical.choose (hex x)
  have hrep (x : ↥P) :
      Incidence x.val (s.1 (rep x).1).val ∧ Incidence x.val (s.2 (rep x).2).val :=
    Classical.choose_spec (hex x)
  let enc : ↥P → ↥Q := fun x => ⟨rep x, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (mem_highCrossPairs X L p _).mpr
      ⟨x.val, (Finset.mem_inter.mp x.property).1, (hrep x).1, (hrep x).2⟩⟩⟩
  have hinj : Function.Injective enc := by
    intro x y hxy
    have he : rep x = rep y := congrArg Subtype.val hxy
    have hy := hrep y
    rw [← he] at hy
    apply Subtype.ext
    exact eq_of_common_incidence_of_ne_lines
      (pencil_ne_complement L p (s.1 (rep x).1) (s.2 (rep x).2))
      (hrep x).1 (hrep x).2 hy.1 hy.2
  exact Finset.card_le_card_of_injective hinj

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace RyserCoveringCounterexample

namespace InjectionSampling

theorem card_pairSample_relation_le
    {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A × B)) (h : ℕ) :
    Fintype.card {z : (Fin h ↪ A) × (Fin h ↪ B) //
      ∀ i, (z.1 i, z.2 i) ∈ S} ≤ S.card ^ h := by
  classical
  let enc : {z : (Fin h ↪ A) × (Fin h ↪ B) //
      ∀ i, (z.1 i, z.2 i) ∈ S} → (Fin h → ↥S) :=
    fun z i => ⟨(z.val.1 i, z.val.2 i), z.property i⟩
  have hinj : Function.Injective enc := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun f : Fin h → ↥S => (f i).val.1) hzw
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun f : Fin h → ↥S => (f i).val.2) hzw
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective enc hinj

theorem prob_restrict_product
    {A B I J K L : Type*}
    [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty (J ↪ A)] [Nonempty (I ↪ A)]
    [Nonempty (L ↪ B)] [Nonempty (K ↪ B)]
    (i : I ↪ J) (j : K ↪ L) (P : (I ↪ A) × (K ↪ B) → Prop) :
    ((FiniteLaw.uniform (J ↪ A)).prod (FiniteLaw.uniform (L ↪ B))).prob
        (fun z => P (restrict i z.1, restrict j z.2)) =
      ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (K ↪ B))).prob P := by
  rw [FiniteLaw.prob_prod_average, FiniteLaw.prob_prod_average]
  calc
    _ = (FiniteLaw.uniform (J ↪ A)).expectation
        (fun a => (FiniteLaw.uniform (K ↪ B)).prob
          (fun b => P (restrict i a, b))) := by
      congr 1
      funext a
      exact prob_restrict j (fun b => P (restrict i a, b))
    _ = _ := by
      simpa only [FiniteLaw.expectation_map] using
        congrArg
          (fun mu : FiniteLaw (I ↪ A) => mu.expectation
            (fun a => (FiniteLaw.uniform (K ↪ B)).prob (fun b => P (a, b))))
          (map_uniform_restrict (Ω := A) i)

theorem prob_pairSample_relation_le
    {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A × B)) (h : ℕ)
    [Nonempty (Fin h ↪ A)] [Nonempty (Fin h ↪ B)] :
    ((FiniteLaw.uniform (Fin h ↪ A)).prod (FiniteLaw.uniform (Fin h ↪ B))).prob
        (fun z => ∀ i, (z.1 i, z.2 i) ∈ S) ≤
      (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  classical
  rw [← FiniteLaw.uniform_prod, FiniteLaw.uniform_prob]
  have hfilter :
      @Finset.filter _ (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
          ∀ i, (z.1 i, z.2 i) ∈ S)
        (fun z => Classical.propDecidable (∀ i, (z.1 i, z.2 i) ∈ S)) Finset.univ =
      Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
        ∀ i, (z.1 i, z.2 i) ∈ S) :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  have hnat : (Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
      ∀ i, (z.1 i, z.2 i) ∈ S)).card ≤ S.card ^ h := by
    simpa only [Fintype.card_subtype] using card_pairSample_relation_le S h
  have hreal : ((Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
      ∀ i, (z.1 i, z.2 i) ∈ S)).card : ℝ) ≤ ((S.card ^ h : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_pow] at hreal
  simpa only [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fin,
    Nat.cast_mul] using
    (div_le_div_of_nonneg_right hreal
      (Nat.cast_nonneg (Fintype.card ((Fin h ↪ A) × (Fin h ↪ B))) :
        (0 : ℝ) ≤ (Fintype.card ((Fin h ↪ A) × (Fin h ↪ B)) : ℝ)))

theorem prob_restricted_relation_le
    {A B : Type*} [Fintype A] [Fintype B] {h t : ℕ}
    [Nonempty (Fin t ↪ A)] [Nonempty (Fin h ↪ A)]
    [Nonempty (Fin t ↪ B)] [Nonempty (Fin h ↪ B)]
    (S : Finset (A × B)) (i j : Fin h ↪ Fin t) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).prob
        (fun z => ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) ≤
      (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  change ((FiniteLaw.uniform (Fin t ↪ A)).prod
      (FiniteLaw.uniform (Fin t ↪ B))).prob
      (fun z => (fun w : (Fin h ↪ A) × (Fin h ↪ B) =>
        ∀ k, (w.1 k, w.2 k) ∈ S) (restrict i z.1, restrict j z.2)) ≤ _
  rw [prob_restrict_product i j (fun w : (Fin h ↪ A) × (Fin h ↪ B) =>
    ∀ k, (w.1 k, w.2 k) ∈ S)]
  exact prob_pairSample_relation_le S h

theorem prob_relation_matching_le
    {A B : Type*} [Fintype A] [Fintype B] {h t : ℕ}
    [Nonempty (Fin t ↪ A)] [Nonempty (Fin h ↪ A)]
    [Nonempty (Fin t ↪ B)] [Nonempty (Fin h ↪ B)]
    (S : Finset (A × B)) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).prob
        (fun z => ∃ i j : Fin h ↪ Fin t, ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) ≤
      (t.descFactorial h : ℝ) ^ 2 * (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  classical
  let mu := (FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))
  calc
    _ ≤ ∑ i : Fin h ↪ Fin t,
        mu.prob (fun z => ∃ j : Fin h ↪ Fin t,
          ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) :=
      mu.prob_exists_le _
    _ ≤ ∑ i : Fin h ↪ Fin t, ∑ j : Fin h ↪ Fin t,
        mu.prob (fun z => ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) := by
      apply Finset.sum_le_sum
      intro i _
      exact mu.prob_exists_le _
    _ ≤ ∑ _i : Fin h ↪ Fin t, ∑ _j : Fin h ↪ Fin t,
        (S.card : ℝ) ^ h /
          ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact prob_restricted_relation_le S i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin]
      ring

end InjectionSampling

end RyserCoveringCounterexample

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

theorem prob_product_average_right
    {A B : Type*} [Fintype A] [Fintype B]
    (mu : FiniteLaw A) (nu : FiniteLaw B) (P : A × B → Prop) :
    (mu.prod nu).prob P = nu.expectation (fun b => mu.prob (fun a => P (a, b))) := by
  rw [FiniteLaw.prob_prod_average]
  unfold FiniteLaw.expectation FiniteLaw.prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P (a, b) <;> simp [hp, mul_comm]

theorem prob_coordinate_product
    {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
    [Nonempty A] [Nonempty B] [Nonempty (I ↪ A)] [Nonempty (J ↪ B)]
    (i : I) (j : J) (P : A × B → Prop) :
    ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (J ↪ B))).prob
        (fun z => P (z.1 i, z.2 j)) =
      ((FiniteLaw.uniform A).prod (FiniteLaw.uniform B)).prob P := by
  rw [FiniteLaw.prob_prod_average, FiniteLaw.prob_prod_average]
  calc
    _ = (FiniteLaw.uniform (I ↪ A)).expectation
        (fun a => (FiniteLaw.uniform B).prob (fun b => P (a i, b))) := by
      congr 1
      funext a
      exact prob_coordinate j (fun b => P (a i, b))
    _ = _ := expectation_coordinate i
      (fun a => (FiniteLaw.uniform B).prob (fun b => P (a, b)))

theorem prob_coordinate_pair_mem
    {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
    [Nonempty A] [Nonempty B] [Nonempty (I ↪ A)] [Nonempty (J ↪ B)]
    (S : Finset (A × B)) (i : I) (j : J) :
    ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (J ↪ B))).prob
        (fun z => (z.1 i, z.2 j) ∈ S) =
      (S.card : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B) := by
  rw [prob_coordinate_product, ← FiniteLaw.uniform_prod, FiniteLaw.uniform_prob]
  have hfilter : @Finset.filter _ (fun z => z ∈ S)
      (fun z => Classical.propDecidable (z ∈ S)) Finset.univ = S := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter, Fintype.card_prod, Nat.cast_mul]

def relationCount {A B : Type*} [Fintype A] [Fintype B] {t : ℕ}
    (S : Finset (A × B)) (z : (Fin t ↪ A) × (Fin t ↪ B)) : ℕ :=
  (Finset.univ.filter fun ij : Fin t × Fin t => (z.1 ij.1, z.2 ij.2) ∈ S).card

theorem expectation_relationCount
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    {t : ℕ} [Nonempty (Fin t ↪ A)] [Nonempty (Fin t ↪ B)]
    (S : Finset (A × B)) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).expectation
        (fun z => (relationCount S z : ℝ)) =
      (t : ℝ) ^ 2 * S.card / ((Fintype.card A : ℝ) * Fintype.card B) := by
  let mu := (FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))
  have hcount (z : (Fin t ↪ A) × (Fin t ↪ B)) :
      (relationCount S z : ℝ) =
        ∑ ij : Fin t × Fin t, if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0 :=
    Finset.natCast_card_filter _ _
  calc
    _ = mu.expectation (fun z =>
        ∑ ij : Fin t × Fin t, if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0) := by
      congr 1
      funext z
      exact hcount z
    _ = ∑ ij : Fin t × Fin t,
        mu.expectation (fun z => if (z.1 ij.1, z.2 ij.2) ∈ S then 1 else 0) :=
      mu.expectation_sum _
    _ = ∑ ij : Fin t × Fin t,
        mu.prob (fun z => (z.1 ij.1, z.2 ij.2) ∈ S) := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [FiniteLaw.prob_eq_expectation]
      congr 1
      funext z
      by_cases hz : (z.1 ij.1, z.2 ij.2) ∈ S <;> simp [hz]
    _ = ∑ _ij : Fin t × Fin t,
        (S.card : ℝ) / ((Fintype.card A : ℝ) * Fintype.card B) := by
      apply Finset.sum_congr rfl
      intro ij _
      exact prob_coordinate_pair_mem S ij.1 ij.2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

theorem prob_hits_finset_le
    {A : Type*} [Fintype A] [Nonempty A] {t : ℕ} [Nonempty (Fin t ↪ A)]
    (S : Finset A) :
    (FiniteLaw.uniform (Fin t ↪ A)).prob (fun z => ∃ i, z i ∈ S) ≤
      (t : ℝ) * S.card / Fintype.card A := by
  have hfilter : @Finset.filter _ (fun a => a ∈ S)
      (fun a => Classical.propDecidable (a ∈ S)) Finset.univ = S := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    _ ≤ ∑ i : Fin t, (FiniteLaw.uniform (Fin t ↪ A)).prob (fun z => z i ∈ S) :=
      (FiniteLaw.uniform (Fin t ↪ A)).prob_exists_le _
    _ = ∑ _i : Fin t, (S.card : ℝ) / Fintype.card A := by
      apply Finset.sum_congr rfl
      intro i _
      rw [prob_coordinate i, FiniteLaw.uniform_prob, hfilter]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.InjectionSampling

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def highUniformLaw (L : Finset (AffineLine F)) (p : ProjectivePoint F) (t : ℕ)
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)] : FiniteLaw (HighSample L p t) :=
  (FiniteLaw.uniform (Fin t ↪ PencilPopulation L p)).prod
    (FiniteLaw.uniform (Fin t ↪ ComplementPopulation L p))

def highFailureBound (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (shapes : Finset (Finset (Point F)))
    (D h t : ℕ) (δ : ℝ) : ℝ :=
  let R := (coverPencil L p).card
  let N := (L \ coverPencil L p).card
  2 * (overlapExcess Incidence X L : ℝ) / (δ * R * N) +
    ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R +
    (shapes.card : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
      ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ))

theorem high_probability_large_survivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} [Nonempty (PencilPopulation L p)] [Nonempty (ComplementPopulation L p)]
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)]
    (δ : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    (highUniformLaw L p t).prob
        (fun s => δ * (t : ℝ) ^ 2 / 2 ≤ (highSurvivorPairCount X L p s : ℝ)) ≤
      2 * (overlapExcess Incidence X L : ℝ) /
        (δ * (coverPencil L p).card * (L \ coverPencil L p).card) := by
  have ht' : 0 < (t : ℝ) := Nat.cast_pos.mpr ht
  have hR : 0 < ((coverPencil L p).card : ℝ) := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := PencilPopulation L p)) :
        (0 : ℝ) < Fintype.card (PencilPopulation L p))
  have hN : 0 < ((L \ coverPencil L p).card : ℝ) := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := ComplementPopulation L p)) :
        (0 : ℝ) < Fintype.card (ComplementPopulation L p))
  have hthreshold : 0 < δ * (t : ℝ) ^ 2 / 2 :=
    div_pos (mul_pos hδ (pow_pos ht' 2)) (by norm_num)
  have hmean : (highUniformLaw L p t).expectation
      (fun s => (highSurvivorPairCount X L p s : ℝ)) =
      (t : ℝ) ^ 2 * (highCrossPairs X L p).card /
        ((coverPencil L p).card * (L \ coverPencil L p).card : ℝ) := by
    have hcount (s : HighSample L p t) :
        highSurvivorPairCount X L p s =
          InjectionSampling.relationCount (highCrossPairs X L p) s := by
      unfold highSurvivorPairCount InjectionSampling.relationCount
      apply congrArg Finset.card
      ext ij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hcount]
    simpa only [highUniformLaw, Fintype.card_coe] using
      (InjectionSampling.expectation_relationCount (highCrossPairs X L p) (t := t))
  have hcard : ((highCrossPairs X L p).card : ℝ) ≤
      (overlapExcess Incidence X L : ℝ) :=
    Nat.cast_le.mpr (highCrossPairs_card_le X L p)
  calc
    _ ≤ (highUniformLaw L p t).expectation
        (fun s => (highSurvivorPairCount X L p s : ℝ)) / (δ * (t : ℝ) ^ 2 / 2) :=
      (highUniformLaw L p t).prob_ge_le_expectation_div _
        (fun s => Nat.cast_nonneg _) hthreshold
    _ = 2 * (highCrossPairs X L p).card /
        (δ * (coverPencil L p).card * (L \ coverPencil L p).card) := by
      rw [hmean]
      field_simp [ne_of_gt hδ, ne_of_gt hR, ne_of_gt hN, ne_of_gt ht']

    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by norm_num))
      (mul_nonneg (mul_nonneg hδ.le hR.le) hN.le)

theorem high_probability_badLines
    (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    [Nonempty (PencilPopulation L p)]
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)] :
    (highUniformLaw L p t).prob (fun s => ∃ i, s.1 i ∈ highBadLines L p s.2) ≤
      ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / (coverPencil L p).card := by
  rw [highUniformLaw, InjectionSampling.prob_product_average_right]
  calc
    _ ≤ (FiniteLaw.uniform (Fin t ↪ ComplementPopulation L p)).expectation
        (fun _ => (t : ℝ) * ((t : ℝ) + (t : ℝ) * t) / (coverPencil L p).card) := by
      apply FiniteLaw.expectation_mono
      intro b
      have hcard : ((highBadLines L p b).card : ℝ) ≤ ((t + t * t : ℕ) : ℝ) :=
        Nat.cast_le.mpr (highBadLines_card_le L p b)
      rw [Nat.cast_add, Nat.cast_mul] at hcard
      calc
        _ ≤ (t : ℝ) * (highBadLines L p b).card / (coverPencil L p).card := by
          simpa only [Fintype.card_coe] using
            InjectionSampling.prob_hits_finset_le (highBadLines L p b)
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [FiniteLaw.expectation_const]
      ring

theorem high_probability_occupancy
    (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (shapes : Finset (Finset (Point F))) (D h : ℕ) {t : ℕ}
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)]
    [Nonempty (Fin h ↪ PencilPopulation L p)]
    [Nonempty (Fin h ↪ ComplementPopulation L p)]
    (hsparse : SparseShapes shapes D) :
    (highUniformLaw L p t).prob (fun s => ∃ S ∈ shapes,
        S ∉ tupleShapes (highTuple L p s) ∧
          2 * D * h < (S ∩ crossPoints (highTuple L p s)).card) ≤
      (shapes.card : ℝ) * (t.descFactorial h : ℝ) ^ 2 *
        ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
        (((coverPencil L p).card.descFactorial h : ℝ) *
          ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
  let mu := highUniformLaw L p t
  have hone (S : ↥shapes) :
      mu.prob (fun s => ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) ≤
        (t.descFactorial h : ℝ) ^ 2 *
          ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
    have hcard : ((highShapePairs S.val L p).card : ℝ) ≤
        ((D * (L \ coverPencil L p).card : ℕ) : ℝ) :=
      Nat.cast_le.mpr (highShapePairs_card_le S.val L p D (hsparse S.val S.property))
    calc
      _ ≤ (t.descFactorial h : ℝ) ^ 2 * (highShapePairs S.val L p).card ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
        simpa only [mu, highUniformLaw, Fintype.card_coe] using
          (InjectionSampling.prob_relation_matching_le
            (highShapePairs S.val L p) (h := h) (t := t))
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard h) (sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _ ≤ mu.prob (fun s => ∃ S : ↥shapes, ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) := by
      apply mu.prob_mono
      intro s hs
      obtain ⟨S, hS, hnot, hlarge⟩ := hs
      exact ⟨⟨S, hS⟩, highShapePairs_matching_of_large
        S L p D h s (hsparse S hS) hnot hlarge⟩
    _ ≤ ∑ S : ↥shapes, mu.prob (fun s => ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) :=
      mu.prob_exists_le _
    _ ≤ ∑ _S : ↥shapes,
        (t.descFactorial h : ℝ) ^ 2 *
          ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) :=
      Finset.sum_le_sum (fun S _ => hone S)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem highConcurrency_exists_admissible
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (hsparse : SparseShapes shapes D) (hδ : 0 < δ)
    (hh : 1 ≤ h) (hht : h ≤ t)
    (htR : t ≤ (coverPencil L p).card)
    (htN : t ≤ (L \ coverPencil L p).card)
    (hfailure : highFailureBound X L p shapes D h t δ < 1) :
    ∃ a : LineTuple F t, (∀ k, a k ∈ L) ∧
      AdmissibleTuple shapes D h a ∧
        ((X ∩ crossPoints a).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (hh.trans hht)
  let : Nonempty (PencilPopulation L p) := Fintype.card_pos_iff.mp
    (by simpa only [Fintype.card_coe] using (lt_of_lt_of_le htpos htR))
  let : Nonempty (ComplementPopulation L p) := Fintype.card_pos_iff.mp
    (by simpa only [Fintype.card_coe] using (lt_of_lt_of_le htpos htN))
  let : Nonempty (Fin t ↪ PencilPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin t) (PencilPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using htR)
  let : Nonempty (Fin t ↪ ComplementPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin t) (ComplementPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using htN)
  let : Nonempty (Fin h ↪ PencilPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin h) (PencilPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]
        using hht.trans htR)
  let : Nonempty (Fin h ↪ ComplementPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin h) (ComplementPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]
        using hht.trans htN)
  let mu := highUniformLaw L p t
  let BadSurvivors : HighSample L p t → Prop :=
    fun s => δ * (t : ℝ) ^ 2 / 2 ≤ (highSurvivorPairCount X L p s : ℝ)
  let BadGeometry : HighSample L p t → Prop :=
    fun s => ∃ i, s.1 i ∈ highBadLines L p s.2
  let BadOccupancy : HighSample L p t → Prop := fun s => ∃ S ∈ shapes,
    S ∉ tupleShapes (highTuple L p s) ∧
      2 * D * h < (S ∩ crossPoints (highTuple L p s)).card
  have hsurvivors := high_probability_large_survivorPairs X L p δ hδ htpos
  have hgeometry := high_probability_badLines L p (t := t)
  have hoccupancy := high_probability_occupancy L p shapes D h (t := t) hsparse
  have hbound : mu.prob (fun s => BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) ≤
      highFailureBound X L p shapes D h t δ := by
    have hu := (mu.prob_union_le BadSurvivors (fun s => BadGeometry s ∨ BadOccupancy s)).trans
      (add_le_add hsurvivors
        ((mu.prob_union_le BadGeometry BadOccupancy).trans
          (add_le_add hgeometry hoccupancy)))
    simpa only [highFailureBound, add_assoc] using hu
  have hsmall := hbound.trans_lt hfailure
  have hex : ∃ s : HighSample L p t,
      ¬ (BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) := by
    by_contra hn
    have hall (s : HighSample L p t) :
        BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s :=
      not_not.mp (fun hs => hn ⟨s, hs⟩)
    have heq : mu.prob (fun s => BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) = 1 := by
      calc
        _ = mu.prob (fun _ => True) := by
          congr 1
          funext s
          exact propext ⟨fun _ => trivial, fun _ => hall s⟩
        _ = 1 := mu.prob_true
    rw [heq] at hsmall
    exact (lt_irrefl (1 : ℝ)) hsmall
  obtain ⟨s, hs⟩ := hex
  have havoid (i : Fin t) : s.1 i ∉ highBadLines L p s.2 := by
    intro hi
    exact hs (Or.inr (Or.inl ⟨i, hi⟩))
  have hgrid := highTuple_grid_of_avoids L p s havoid
  have hocc : ∀ S ∈ shapes, S ∉ tupleShapes (highTuple L p s) →
      (S ∩ crossPoints (highTuple L p s)).card ≤ 2 * D * h := by
    intro S hS hnot
    by_contra hlarge
    exact hs (Or.inr (Or.inr ⟨S, hS, hnot, lt_of_not_ge hlarge⟩))
  have hpair : (highSurvivorPairCount X L p s : ℝ) < δ * (t : ℝ) ^ 2 / 2 :=
    lt_of_not_ge (fun he => hs (Or.inl he))
  refine ⟨highTuple L p s, highTuple_mem L p s, ⟨hgrid.1, hgrid.2, hocc⟩, ?_⟩
  exact (Nat.cast_le.mpr (highSurvivorPoints_card_le X L p s)).trans_lt hpair

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.LineCover

theorem half_pow_le_descFactorial (n k : ℕ) (h : 2 * k ≤ n) :
    ((n : ℝ) / 2) ^ k ≤ (n.descFactorial k : ℝ) := by
  have hk : k ≤ n := (Nat.le_mul_of_pos_left k (by decide : 0 < 2)).trans h
  have hkn : k ≤ n + 1 := hk.trans (Nat.le_succ n)
  have hr : (2 : ℝ) * k ≤ n := by exact_mod_cast h
  have hbase : (n : ℝ) / 2 ≤ ((n + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
    linarith
  calc
    ((n : ℝ) / 2) ^ k ≤ (((n + 1 - k : ℕ) : ℝ)) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ (n.descFactorial k : ℝ) := by
      exact_mod_cast Nat.pow_sub_le_descFactorial n k

theorem low_occupancy_quotient_le (m D R t h : ℕ)
    (hm : 0 < m) (hlarge : 4 * h ≤ m) :
    (t : ℝ) ^ (2 * h) * ((m : ℝ) * D * R) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤
      (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : ((m : ℝ) / 2) ^ (2 * h) ≤ (m.descFactorial (2 * h) : ℝ) :=
    half_pow_le_descFactorial m (2 * h) (by simpa only [← Nat.mul_assoc] using hlarge)
  have hpos : 0 < ((m : ℝ) / 2) ^ (2 * h) := by positivity
  calc
    _ ≤ (t : ℝ) ^ (2 * h) * ((m : ℝ) * D * R) ^ h /
        (((m : ℝ) / 2) ^ (2 * h)) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = ((t : ℝ) ^ 2 * ((m : ℝ) * D * R) / ((m : ℝ) / 2) ^ 2) ^ h := by
      simp only [div_pow, mul_pow, pow_mul]
    _ = _ := by
      congr 1
      field_simp
      ring

theorem high_occupancy_quotient_le (R N D t h : ℕ)
    (hR : 0 < R) (hN : 0 < N) (hRlarge : 2 * h ≤ R) (hNlarge : 2 * h ≤ N) :
    (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : ((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h ≤
      (R.descFactorial h : ℝ) * (N.descFactorial h : ℝ) :=
    mul_le_mul (half_pow_le_descFactorial R h hRlarge)
      (half_pow_le_descFactorial N h hNlarge) (by positivity) (by positivity)
  have hpos : 0 < ((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h := by positivity
  calc
    _ ≤ (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h /
        (((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = ((t : ℝ) ^ 2 * ((D : ℝ) * N) / (((R : ℝ) / 2) * ((N : ℝ) / 2))) ^ h := by
      simp only [div_pow, mul_pow, pow_mul]
    _ = _ := by
      congr 1
      field_simp
      ring

end RyserCoveringCounterexample.LineCover

end OAI
end

section
namespace OAI

namespace RyserCoveringCounterexample.LineCover

private theorem half_sq_le_descFactorial_two (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) ^ 2 / 2 ≤ (m.descFactorial 2 : ℝ) := by
  have hm1 : 1 ≤ m := (by decide : 1 ≤ 2).trans hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalf : (m : ℝ) / 2 ≤ (m : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg m)
  have hfactor : m.descFactorial 2 = (m - 1) * m := by
    simpa only [Nat.descFactorial_one] using Nat.descFactorial_succ m 1
  rw [hfactor, Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one]
  nlinarith only [hmul]

private theorem half_le_nat_sub_cast (m j : ℕ) (h : 2 * j ≤ m) :
    (m : ℝ) / 2 ≤ ((m - j : ℕ) : ℝ) := by
  have hjm : j ≤ m := (Nat.le_mul_of_pos_left j (by decide : 0 < 2)).trans h
  have hR : (2 : ℝ) * j ≤ m := by exact_mod_cast h
  rw [Nat.cast_sub hjm]
  linarith

theorem low_sampling_failure_le_coarse (m D R t h K : ℕ) (P δ : ℝ)
    (hm : 4 ≤ m) (hδ : 0 < δ) (hlarge : 4 * h ≤ m) (hP : 0 ≤ P) :
    2 * P / (δ * (m.descFactorial 2 : ℝ)) +
      ((2 * t).descFactorial 2 : ℝ) * R / ((m - 1 : ℕ) : ℝ) +
      ((2 * t).descFactorial 3 : ℝ) * R / ((m - 2 : ℕ) : ℝ) +
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤
    4 * P / (δ * (m : ℝ) ^ 2) +
      8 * (t : ℝ) ^ 2 * R / m +
      16 * (t : ℝ) ^ 3 * R / m +
      (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hpairden : δ * ((m : ℝ) ^ 2 / 2) ≤ δ * (m.descFactorial 2 : ℝ) :=
    mul_le_mul_of_nonneg_left
      (half_sq_le_descFactorial_two m ((by decide : 2 ≤ 4).trans hm)) hδ.le
  have hpair : 2 * P / (δ * (m.descFactorial 2 : ℝ)) ≤
      4 * P / (δ * (m : ℝ) ^ 2) := by
    calc
      _ ≤ 2 * P / (δ * ((m : ℝ) ^ 2 / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpairden
      _ = _ := by
        field_simp [hδ.ne', hmR.ne']
        ring
  have htwo : ((2 * t).descFactorial 2 : ℝ) ≤ 4 * (t : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 * t : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast Nat.descFactorial_le_pow (2 * t) 2
      _ = _ := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hthree : ((2 * t).descFactorial 3 : ℝ) ≤ 8 * (t : ℝ) ^ 3 := by
    calc
      _ ≤ ((2 * t : ℕ) : ℝ) ^ 3 := by
        exact_mod_cast Nat.descFactorial_le_pow (2 * t) 3
      _ = _ := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hsub1 : (m : ℝ) / 2 ≤ ((m - 1 : ℕ) : ℝ) :=
    half_le_nat_sub_cast m 1 ((by decide : 2 * 1 ≤ 4).trans hm)
  have hsub2 : (m : ℝ) / 2 ≤ ((m - 2 : ℕ) : ℝ) :=
    half_le_nat_sub_cast m 2 hm
  have hparallel : ((2 * t).descFactorial 2 : ℝ) * R /
      ((m - 1 : ℕ) : ℝ) ≤ 8 * (t : ℝ) ^ 2 * R / m := by
    calc
      _ ≤ (4 * (t : ℝ) ^ 2 * R) / ((m : ℝ) / 2) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg R)) (by positivity) hsub1
      _ = _ := by
        field_simp [hmR.ne']
        ring
  have hconcurrent : ((2 * t).descFactorial 3 : ℝ) * R /
      ((m - 2 : ℕ) : ℝ) ≤ 16 * (t : ℝ) ^ 3 * R / m := by
    calc
      _ ≤ (8 * (t : ℝ) ^ 3 * R) / ((m : ℝ) / 2) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right hthree (Nat.cast_nonneg R)) (by positivity) hsub2
      _ = _ := by
        field_simp [hmR.ne']
        ring
  have hoccupancy :
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
          (m.descFactorial (2 * h) : ℝ) ≤
        (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
    simpa only [Nat.cast_mul, mul_assoc, mul_div_assoc] using
      mul_le_mul_of_nonneg_left (low_occupancy_quotient_le m D R t h hmpos hlarge)
        (Nat.cast_nonneg K)
  exact add_le_add (add_le_add (add_le_add hpair hparallel) hconcurrent) hoccupancy

theorem high_occupancy_term_le_coarse (R N D t h K : ℕ)
    (hR : 0 < R) (hN : 0 < N) (hRlarge : 2 * h ≤ R) (hNlarge : 2 * h ≤ N) :
    (K : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h := by
  have hfall : (t.descFactorial h : ℝ) ≤ (t : ℝ) ^ h := by
    exact_mod_cast Nat.descFactorial_le_pow t h
  have hfall2 : (t.descFactorial h : ℝ) ^ 2 ≤ (t : ℝ) ^ (2 * h) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hfall 2).trans_eq
      (pow_mul' (t : ℝ) 2 h).symm
  have hnum : (t.descFactorial h : ℝ) ^ 2 * ((D : ℝ) * N) ^ h ≤
      (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h :=
    mul_le_mul_of_nonneg_right hfall2 (by positivity)
  have hratio :
      (t.descFactorial h : ℝ) ^ 2 * ((D : ℝ) * N) ^ h /
          ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
        (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h :=
    (div_le_div_of_nonneg_right hnum
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans
        (high_occupancy_quotient_le R N D t h hR hN hRlarge hNlarge)
  simpa only [Nat.cast_mul, mul_assoc, mul_div_assoc] using
    mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg K)

end RyserCoveringCounterexample.LineCover

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

def lowFailureEnvelope (D : ℕ) (δ A κ q : ℝ) : ℝ :=
  let h := 10 * (D + 1)
  let t := (logarithmicSampleSize A q : ℝ)
  (16 / δ) * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) +
    (16 * (t ^ 2 * q ^ (-(1 / 2 - κ / 4))) +
      32 * (t ^ 3 * q ^ (-(1 / 2 - κ / 4)))) +
    ((D : ℝ) * (8 * (D : ℝ)) ^ h) *
      (t ^ (2 * h) * q ^ (-((h : ℝ) * (1 / 2 - κ / 4) - D)))

def highFailureEnvelope (D : ℕ) (δ ρ A κ q : ℝ) : ℝ :=
  let h := 10 * (D + 1)
  let t := (logarithmicSampleSize A q : ℝ)
  (4 * ((D : ℝ) + 4) / (δ * ρ)) * q ^ (-(3 * κ / 20)) +
    (t ^ 2 * q ^ (-(1 / 2 + κ / 4)) +
      t ^ 3 * q ^ (-(1 / 2 + κ / 4))) +
    ((D : ℝ) * (4 * (D : ℝ)) ^ h) *
      (t ^ (2 * h) * q ^ (-((h : ℝ) * (1 / 2 + κ / 4) - D)))

theorem low_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : κ ≤ 1) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 - κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_nonneg (by positivity : 0 ≤ (D : ℝ) + 1)
    (sub_nonneg.mpr hκ)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem high_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 + κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_pos (by positivity : 0 < (D : ℝ) + 1) hκ
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem tendsto_lowFailureEnvelope_atTop (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    Tendsto (lowFailureEnvelope D δ A κ) atTop (𝓝 0) := by
  have hfirst := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 7 * κ / 30)).const_mul ((D : ℝ) + 4)
  have hsecond := tendsto_rpow_neg_atTop (by positivity : 0 < 3 * κ / 4)
  have hsurvivors := (hfirst.add hsecond).const_mul (16 / δ)
  have hdecay : 0 < (1 / 2 : ℝ) - κ / 4 := by linarith
  have hparallel := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).const_mul
    (16 : ℝ)
  have hconcurrent := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay).const_mul
    (32 : ℝ)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (low_occupancy_decay_pos D hκone)).const_mul
      ((D : ℝ) * (8 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold lowFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add (hparallel.add hconcurrent)).add hoccupancy

theorem tendsto_highFailureEnvelope_atTop (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    Tendsto (highFailureEnvelope D δ ρ A κ) atTop (𝓝 0) := by
  have hsurvivors := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 3 * κ / 20)).const_mul (4 * ((D : ℝ) + 4) / (δ * ρ))
  have hdecay : 0 < (1 / 2 : ℝ) + κ / 4 := by positivity
  have hgeometry := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).add
    (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (high_occupancy_decay_pos D hκ)).const_mul
      ((D : ℝ) * (4 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold highFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add hgeometry).add hoccupancy

theorem eventually_lowFailureEnvelope_lt_one (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∀ᶠ q : ℝ in atTop, lowFailureEnvelope D δ A κ q < 1 :=
  (tendsto_order.mp (tendsto_lowFailureEnvelope_atTop D δ hA hκ hκone)).2 1
    (by norm_num)

theorem eventually_highFailureEnvelope_lt_one (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop, highFailureEnvelope D δ ρ A κ q < 1 :=
  (tendsto_order.mp (tendsto_highFailureEnvelope_atTop D δ ρ hA hκ)).2 1
    (by norm_num)

theorem low_concurrency_ratio_le {q m R κ : ℝ} (hq : 0 < q)
    (hm : q / 2 ≤ m) (hR : R ≤ q ^ (1 / 2 + κ / 4)) :
    R / m ≤ 2 * q ^ (-(1 / 2 - κ / 4)) := by
  calc
    R / m ≤ q ^ (1 / 2 + κ / 4) / (q / 2) :=
      div_le_div₀ (Real.rpow_nonneg hq.le _) hR (by positivity) hm
    _ = 2 * (q ^ (1 / 2 + κ / 4) / q) := by
      field_simp [hq.ne']

    _ = 2 * q ^ (-(1 / 2 - κ / 4)) := by
      rw [← Real.rpow_sub_one hq.ne']
      congr 2
      ring

theorem high_concurrency_inverse_le {q R κ : ℝ} (hq : 0 < q)
    (hR : q ^ (1 / 2 + κ / 4) ≤ R) :
    1 / R ≤ q ^ (-(1 / 2 + κ / 4)) := by
  calc
    1 / R ≤ 1 / q ^ (1 / 2 + κ / 4) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hq _) hR
    _ = q ^ (-(1 / 2 + κ / 4)) := by rw [Real.rpow_neg hq.le, one_div]

theorem sampling_occupancy_le_power (D h t : ℕ) {q K B C β : ℝ}
    (hq : 0 < q) (hK0 : 0 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hK : K ≤ (D : ℝ) * q ^ (D : ℝ))
    (hbase : B ≤ C * (t : ℝ) ^ 2 * q ^ (-β)) :
    K * B ^ h ≤ ((D : ℝ) * C ^ h) *
      ((t : ℝ) ^ (2 * h) * q ^ (-((h : ℝ) * β - D))) := by
  let _ := hK0
  let _ := hC
  have hp := pow_le_pow_left₀ hB hbase h
  have hjoin : q ^ (D : ℝ) * (q ^ (-β)) ^ h =
      q ^ (-((h : ℝ) * β - D)) := by
    rw [← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq]
    congr 1
    ring
  calc
    K * B ^ h ≤ ((D : ℝ) * q ^ (D : ℝ)) *
        (C * (t : ℝ) ^ 2 * q ^ (-β)) ^ h :=
      mul_le_mul hK hp (pow_nonneg hB _) (by positivity)
    _ = ((D : ℝ) * C ^ h) * (t : ℝ) ^ (2 * h) *
        (q ^ (D : ℝ) * (q ^ (-β)) ^ h) := by
      simp only [mul_pow, pow_mul]
      ring
    _ = _ := by rw [hjoin]; ring

theorem high_survivor_term_le {q E R N δ ρ κ : ℝ} (D : ℕ)
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ R) (hN : ρ * q / 2 ≤ N) :
    2 * E / (δ * R * N) ≤
      (4 * ((D : ℝ) + 4) / (δ * ρ)) * q ^ (-(3 * κ / 20)) := by
  let _ := hE0
  have hR0 : 0 < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hden : δ * q ^ (1 / 2 + κ / 4) * (ρ * q / 2) ≤ δ * R * N :=
    mul_le_mul (mul_le_mul_of_nonneg_left hR hδ.le) hN (by positivity)
      (mul_nonneg hδ.le hR0.le)
  have hratio : q ^ (3 / 2 + κ / 10) /
      (q ^ (1 / 2 + κ / 4) * q) = q ^ (-(3 * κ / 20)) := by
    rw [← Real.rpow_add_one hq.ne', ← Real.rpow_sub hq]
    congr 1
    ring
  calc
    2 * E / (δ * R * N) ≤
        (2 * (((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))) /
          (δ * q ^ (1 / 2 + κ / 4) * (ρ * q / 2)) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hden
    _ = (4 * ((D : ℝ) + 4) / (δ * ρ)) *
        (q ^ (3 / 2 + κ / 10) / (q ^ (1 / 2 + κ / 4) * q)) := by
      field_simp
      ring
    _ = _ := by rw [hratio]

theorem low_coarse_failure_le_envelope (D m R K : ℕ) {δ A κ q P : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hm : q / 2 ≤ (m : ℝ))
    (hR : (R : ℝ) ≤ q ^ (1 / 2 + κ / 4))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ))
    (hP : P / (m : ℝ) ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) :
    let t := (logarithmicSampleSize A q : ℝ)
    let h := 10 * (D + 1)
    4 * P / (δ * (m : ℝ) ^ 2) + 8 * t ^ 2 * R / m +
      16 * t ^ 3 * R / m + (K : ℝ) * (4 * (D : ℝ) * t ^ 2 * R / m) ^ h ≤
      lowFailureEnvelope D δ A κ q := by
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hratio := low_concurrency_ratio_le hq hm hR
  have hpair : 4 * P / (δ * (m : ℝ) ^ 2) ≤
      (16 / δ) * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 4 / δ)
    calc
      _ = (4 / δ) * (P / (m : ℝ) ^ 2) := by
        field_simp [hδ.ne', hm0.ne']

      _ ≤ (4 / δ) *
          (4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) := hh
      _ = _ := by ring
  have hparallel : 8 * (t : ℝ) ^ 2 * R / m ≤
      16 * ((t : ℝ) ^ 2 * q ^ (-(1 / 2 - κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 8 * (t : ℝ) ^ 2)
    calc
      _ = (8 * (t : ℝ) ^ 2) * ((R : ℝ) / m) := by ring
      _ ≤ (8 * (t : ℝ) ^ 2) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hconcurrent : 16 * (t : ℝ) ^ 3 * R / m ≤
      32 * ((t : ℝ) ^ 3 * q ^ (-(1 / 2 - κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 16 * (t : ℝ) ^ 3)
    calc
      _ = (16 * (t : ℝ) ^ 3) * ((R : ℝ) / m) := by ring
      _ ≤ (16 * (t : ℝ) ^ 3) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hbase : 4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m ≤
      (8 * (D : ℝ)) * (t : ℝ) ^ 2 * q ^ (-(1 / 2 - κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hratio
      (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2)
    calc
      _ = (4 * (D : ℝ) * (t : ℝ) ^ 2) * ((R : ℝ) / m) := by ring
      _ ≤ (4 * (D : ℝ) * (t : ℝ) ^ 2) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hoccupancy := sampling_occupancy_le_power D h t hq (Nat.cast_nonneg K)
    (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m)
    (by positivity : 0 ≤ 8 * (D : ℝ)) hK hbase
  dsimp only [lowFailureEnvelope]
  dsimp only [t, h] at hparallel hconcurrent hoccupancy
  linarith

theorem high_coarse_failure_le_envelope (D R N K : ℕ) {δ ρ A κ q E : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ (R : ℝ)) (hN : ρ * q / 2 ≤ (N : ℝ))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ)) :
    let t := (logarithmicSampleSize A q : ℝ)
    let h := 10 * (D + 1)
    2 * E / (δ * R * N) + (t ^ 2 + t ^ 3) / R +
      (K : ℝ) * (4 * (D : ℝ) * t ^ 2 / R) ^ h ≤
      highFailureEnvelope D δ ρ A κ q := by
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hsurvivors := high_survivor_term_le D hq hδ hρ hE0 hE hR hN
  have hinverse := high_concurrency_inverse_le hq hR
  have hgeometry : ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R ≤
      (t : ℝ) ^ 2 * q ^ (-(1 / 2 + κ / 4)) +
        (t : ℝ) ^ 3 * q ^ (-(1 / 2 + κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hinverse
      (by positivity : 0 ≤ (t : ℝ) ^ 2 + (t : ℝ) ^ 3)
    calc
      _ = ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) * (1 / (R : ℝ)) := by ring
      _ ≤ ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) * q ^ (-(1 / 2 + κ / 4)) := hh
      _ = _ := by ring
  have hbase : 4 * (D : ℝ) * (t : ℝ) ^ 2 / R ≤
      (4 * (D : ℝ)) * (t : ℝ) ^ 2 * q ^ (-(1 / 2 + κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hinverse
      (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2)
    calc
      _ = (4 * (D : ℝ) * (t : ℝ) ^ 2) * (1 / (R : ℝ)) := by ring
      _ ≤ (4 * (D : ℝ) * (t : ℝ) ^ 2) * q ^ (-(1 / 2 + κ / 4)) := hh
      _ = _ := by ring
  have hoccupancy := sampling_occupancy_le_power D h t hq (Nat.cast_nonneg K)
    (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2 / R)
    (by positivity : 0 ≤ 4 * (D : ℝ)) hK hbase
  dsimp only [highFailureEnvelope]
  dsimp only [t, h] at hgeometry hoccupancy
  linarith

theorem low_sampling_failure_le_envelope (D m R K : ℕ) {δ A κ q P : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hm : q / 2 ≤ (m : ℝ))
    (hm4 : 4 ≤ m) (hlarge : 4 * (10 * (D + 1)) ≤ m) (hP0 : 0 ≤ P)
    (hR : (R : ℝ) ≤ q ^ (1 / 2 + κ / 4))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ))
    (hP : P / (m : ℝ) ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) :
    let t := logarithmicSampleSize A q
    let h := 10 * (D + 1)
    2 * P / (δ * (m.descFactorial 2 : ℝ)) +
      ((2 * t).descFactorial 2 : ℝ) * R / ((m - 1 : ℕ) : ℝ) +
      ((2 * t).descFactorial 3 : ℝ) * R / ((m - 2 : ℕ) : ℝ) +
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤ lowFailureEnvelope D δ A κ q :=
  (low_sampling_failure_le_coarse m D R (logarithmicSampleSize A q)
    (10 * (D + 1)) K P δ hm4 hδ hlarge hP0).trans
      (low_coarse_failure_le_envelope D m R K hq hδ hm hR hK hP)

theorem high_sampling_failure_le_envelope (D R N K : ℕ) {δ ρ A κ q E : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ (R : ℝ)) (hN : ρ * q / 2 ≤ (N : ℝ))
    (hRlarge : 2 * (10 * (D + 1)) ≤ R) (hNlarge : 2 * (10 * (D + 1)) ≤ N)
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ)) :
    let t := logarithmicSampleSize A q
    let h := 10 * (D + 1)
    2 * E / (δ * R * N) + ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R +
      (K : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      highFailureEnvelope D δ ρ A κ q := by
  have hR0 : 0 < R := by
    exact_mod_cast lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hN0 : 0 < N := by
    have hNreal : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
    exact_mod_cast hNreal
  exact (add_le_add (le_refl _)
    (high_occupancy_term_le_coarse R N D (logarithmicSampleSize A q)
      (10 * (D + 1)) K hR0 hN0 hRlarge hNlarge)).trans
        (high_coarse_failure_le_envelope (A := A) D R N K hq hδ hρ hE0 hE hR hN hK)

theorem eventually_sampleSize_le_mul_rpow {A a c : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ q : ℝ in atTop, (logarithmicSampleSize A q : ℝ) ≤ c * q ^ a := by
  have hlim := tendsto_sampleSize_pow_mul_rpow_neg_atTop 1 hA ha
  filter_upwards [(tendsto_order.mp hlim).2 c hc,
    eventually_gt_atTop (0 : ℝ)] with q hsmall hq
  rw [pow_one, Real.rpow_neg hq.le, ← div_eq_mul_inv] at hsmall
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hq _)).mp hsmall).le

theorem eventually_sampling_size_bounds (D : ℕ) {A ρ κ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop,
      8 ≤ q ∧
      10 * (D + 1) ≤ logarithmicSampleSize A q ∧
      (4 * (10 * (D + 1)) : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q ^ (1 / 2 + κ / 4) ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ ρ * q / 2 := by
  have hlog := (tendsto_logarithmicSampleSize_atTop hA).eventually_ge_atTop
    (((10 * (D + 1) : ℕ) : ℝ))
  have hlinear := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hpencil := eventually_sampleSize_le_mul_rpow hA
    (by positivity : 0 < (1 / 2 : ℝ) + κ / 4) (by norm_num : (0 : ℝ) < 1 / 2)
  have hcomplement := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < ρ / 4)
  filter_upwards [eventually_ge_atTop (8 : ℝ), hlog, hlinear, hpencil, hcomplement,
    eventually_ge_atTop (8 * (10 * ((D : ℝ) + 1)))] with
      q hq ht hlo hhi hco hlarge
  have htNat : 10 * (D + 1) ≤ logarithmicSampleSize A q := by exact_mod_cast ht
  rw [Real.rpow_one] at hlo hco
  refine ⟨hq, htNat, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

def rigidityBudget (D : ℕ) (κ q : ℝ) : ℝ :=
  2 * q ^ (3 / 2 + κ / 10) + ((D : ℝ) + 2) * q

theorem rigidityBudget_eq_errors (D : ℕ) {κ q : ℝ} (hq : 0 < q) :
    rigidityBudget D κ q =
      q ^ (3 / 2 + κ / 10) + q * ((D : ℝ) + q ^ (1 / 2 + κ / 10)) + 2 * q := by
  have hmul : q * q ^ (1 / 2 + κ / 10) = q ^ (3 / 2 + κ / 10) := by
    calc
      _ = q ^ (1 : ℝ) * q ^ (1 / 2 + κ / 10) := by rw [Real.rpow_one]
      _ = q ^ ((1 : ℝ) + (1 / 2 + κ / 10)) := (Real.rpow_add hq _ _).symm
      _ = _ := by congr 1; ring
  unfold rigidityBudget
  rw [mul_add, hmul]
  ring

theorem rigidityBudget_le (D : ℕ) {κ q : ℝ} (hκ : 0 ≤ κ) (hq : 1 ≤ q) :
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) := by
  have hpow : q ≤ q ^ (3 / 2 + κ / 10) := by
    calc
      q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (D : ℝ) + 2 by positivity)
  unfold rigidityBudget
  nlinarith only [hmul]

private theorem eventually_mul_rpow_le_mul (C c a b : ℝ)
    (hc : 0 < c) (hab : a < b) :
    ∀ᶠ q : ℝ in atTop, C * q ^ a ≤ c * q ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hgap).eventually_ge_atTop (C / c)] with q hq hlarge
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hC : C ≤ q ^ (b - a) * c := (div_le_iff₀ hc).mp hlarge
  calc
    C * q ^ a ≤ (q ^ (b - a) * c) * q ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hqpos.le _)
    _ = c * q ^ b := by
      rw [mul_comm (q ^ (b - a)) c, mul_assoc, ← Real.rpow_add hqpos]
      rw [show b - a + a = b by ring]

private theorem eventually_rigidityBudget_div_le (D : ℕ) {δ c κ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, rigidityBudget D κ q / (δ * q) ≤ c * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul ((D : ℝ) + 4) (δ * c / 2)
    (3 / 2 + κ / 10) 2 (by positivity) (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with q hq hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply (div_le_iff₀ (mul_pos hδ hqpos)).2
  calc
    rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
      rigidityBudget_le D hκ hq
    _ ≤ (δ * c / 2) * q ^ (2 : ℝ) := hsmallq
    _ = (c * q / 2) * (δ * q) := by rw [Real.rpow_two]; ring

theorem eventually_rigidityBudget_div_le_min (D : ℕ) {δ ρ κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      rigidityBudget D κ q / (δ * q) ≤ min (q / 2) (ρ * q / 2) := by
  filter_upwards [eventually_rigidityBudget_div_le D hδ zero_lt_one hκ.le hκmax,
    eventually_rigidityBudget_div_le D hδ hρ hκ.le hκmax] with q hleft hright
  exact le_min (by simpa only [one_mul] using hleft) hright

theorem eventually_rigidity_heavy_bounds (D : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop,
      1 < q ^ (1 / 2 - κ / 3) ∧
        rigidityBudget D κ q / (q ^ (1 / 2 - κ / 3) - 1) ≤ q ^ (1 + κ) := by
  have hd : 0 < (1 / 2 : ℝ) - κ / 3 := by linarith
  have hgap : (3 / 2 : ℝ) + κ / 10 < (1 + κ) + (1 / 2 - κ / 3) := by
    linarith
  have hsmall := eventually_mul_rpow_le_mul (2 * ((D : ℝ) + 4)) 1
    (3 / 2 + κ / 10) ((1 + κ) + (1 / 2 - κ / 3)) zero_lt_one hgap
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hd).eventually_ge_atTop 2, hsmall]
      with q hq hT hsmallq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [one_mul, Real.rpow_add hqpos (1 + κ) (1 / 2 - κ / 3)] at hsmallq
  have hscaled := mul_le_mul_of_nonneg_left hT
    (Real.rpow_nonneg hqpos.le (1 + κ))
  constructor
  · linarith
  · apply (div_le_iff₀ (by linarith : 0 < q ^ (1 / 2 - κ / 3) - 1)).2
    calc
      rigidityBudget D κ q ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10) :=
        rigidityBudget_le D hκ.le hq
      _ ≤ q ^ (1 + κ) * (q ^ (1 / 2 - κ / 3) - 1) := by
        nlinarith only [hsmallq, hscaled]

theorem eventually_line_error_le_half {δ κ : ℝ}
    (hδ : 0 < δ) (hκmax : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, q ^ (1 / 2 + κ / 10) ≤ δ * q / 2 := by
  have hsmall := eventually_mul_rpow_le_mul 1 (δ / 2) (1 / 2 + κ / 10) 1
    (by positivity) (by linarith)
  filter_upwards [hsmall] with q hsmallq
  calc
    q ^ (1 / 2 + κ / 10) ≤ (δ / 2) * q ^ (1 : ℝ) := by
      simpa only [one_mul] using hsmallq
    _ = δ * q / 2 := by rw [Real.rpow_one]; ring

theorem pair_mass_ratio_le_coarse (D : ℕ) {q κ m B R P : ℝ}
    (hq : 1 ≤ q)
    (hB : B ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : R ≤ q ^ (1 / 2 + κ / 4)) (hm : q / 2 ≤ m)
    (hP : P ≤ q ^ (1 / 2 - κ / 3) * B + R * q ^ (3 / 2 - κ)) :
    P / m ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have he₁ : (1 / 2 - κ / 3) + (3 / 2 + κ / 10) = 2 - 7 * κ / 30 := by ring
  have he₂ : (1 / 2 + κ / 4) + (3 / 2 - κ) = 2 - 3 * κ / 4 := by ring
  have hnum : P ≤ ((D : ℝ) + 4) * q ^ (2 - 7 * κ / 30) +
      q ^ (2 - 3 * κ / 4) := by
    calc
      P ≤ q ^ (1 / 2 - κ / 3) * B + R * q ^ (3 / 2 - κ) := hP
      _ ≤ q ^ (1 / 2 - κ / 3) * (((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10)) +
          q ^ (1 / 2 + κ / 4) * q ^ (3 / 2 - κ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hqpos.le _))
          (mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg hqpos.le _))
      _ = _ := by
        rw [mul_left_comm (q ^ (1 / 2 - κ / 3)) ((D : ℝ) + 4)
          (q ^ (3 / 2 + κ / 10))]
        simp only [← Real.rpow_add hqpos, he₁, he₂]
  have hden : (q / 2) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
  have hdiv (a : ℝ) : q ^ a / q ^ 2 = q ^ (a - 2) :=
    (Real.rpow_sub_natCast hqpos.ne' a 2).symm
  calc
    P / m ^ 2 ≤
        (((D : ℝ) + 4) * q ^ (2 - 7 * κ / 30) + q ^ (2 - 3 * κ / 4)) /
          (q / 2) ^ 2 :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 * (((D : ℝ) + 4) * (q ^ (2 - 7 * κ / 30) / q ^ 2) +
        q ^ (2 - 3 * κ / 4) / q ^ 2) := by
      field_simp [hqpos.ne']
      ring
    _ = _ := by
      rw [hdiv (2 - 7 * κ / 30), hdiv (2 - 3 * κ / 4),
        show (2 - 7 * κ / 30) - 2 = -(7 * κ / 30) by ring,
        show (2 - 3 * κ / 4) - 2 = -(3 * κ / 4) by ring]

theorem rigidity_pair_ratio_le (D : ℕ) {q κ m E R P : ℝ}
    (hq : 1 ≤ q) (hκ : 0 ≤ κ) (hm : q / 2 ≤ m)
    (hR : R ≤ q ^ (1 / 2 + κ / 4)) (hE : E ≤ rigidityBudget D κ q)
    (hpair : P ≤ q ^ (1 / 2 - κ / 3) * E + R * q ^ (3 / 2 - κ)) :
    P / m ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) :=
  pair_mass_ratio_le_coarse D hq (hE.trans (rigidityBudget_le D hκ hq)) hR hm hpair

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

structure RigidityParameters (D : ℕ) (δ ρ A κ q : ℝ) : Prop where
  q_one : 1 ≤ q
  m_four : 4 ≤ q / 2
  m_h : 4 * ((10 * (D + 1) : ℕ) : ℝ) ≤ q / 2
  m_t : 2 * (logarithmicSampleSize A q : ℝ) ≤ q / 2
  h_t : 10 * (D + 1) ≤ logarithmicSampleSize A q
  r_t : (logarithmicSampleSize A q : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  r_h : 2 * ((10 * (D + 1) : ℕ) : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  n_t : (logarithmicSampleSize A q : ℝ) ≤ ρ * q / 2
  n_h : 2 * ((10 * (D + 1) : ℕ) : ℝ) ≤ ρ * q / 2
  T_one : 1 < q ^ (1 / 2 - κ / 3)
  gap_half : rigidityBudget D κ q / (δ * q) ≤ q / 2
  gap_rho : rigidityBudget D κ q / (δ * q) ≤ ρ * q / 2
  heavy : rigidityBudget D κ q / (q ^ (1 / 2 - κ / 3) - 1) ≤ q ^ (1 + κ)
  low : lowFailureEnvelope D δ A κ q < 1
  high : highFailureEnvelope D δ ρ A κ q < 1
  lineerror : q ^ (1 / 2 + κ / 10) ≤ δ * q / 2

theorem eventually_rigidityParameters (D : ℕ) {δ ρ A κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 0 < A) (hκ : 0 < κ)
    (hκsmall : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, RigidityParameters D δ ρ A κ q := by
  have hsizes := eventually_sampling_size_bounds D hA hρ hκ
  have hgaps := eventually_rigidityBudget_div_le_min D hδ hρ hκ hκsmall
  have hheavy := eventually_rigidity_heavy_bounds D hκ hκsmall
  have hlow := eventually_lowFailureEnvelope_lt_one D δ hA hκ
    (show κ ≤ 1 by linarith)
  have hhigh := eventually_highFailureEnvelope_lt_one D δ ρ hA hκ
  have hline := eventually_line_error_le_half hδ hκsmall
  filter_upwards [hsizes, hgaps, hheavy, hlow, hhigh, hline] with
    q hsize hgap hheavyq hlo hhi hlin
  rcases hsize with ⟨hq, hht, hmh, hmt, hrt, hnt⟩
  have hhtR : ((10 * (D + 1) : ℕ) : ℝ) ≤ (logarithmicSampleSize A q : ℝ) := by
    exact_mod_cast hht
  have ht0 : (0 : ℝ) ≤ logarithmicSampleSize A q := Nat.cast_nonneg _
  refine {
    q_one := by linarith
    m_four := by linarith
    m_h := ?_
    m_t := hmt
    h_t := hht
    r_t := by linarith
    r_h := by linarith
    n_t := by linarith
    n_h := by linarith
    T_one := hheavyq.1
    gap_half := hgap.trans (min_le_left _ _)
    gap_rho := hgap.trans (min_le_right _ _)
    heavy := hheavyq.2
    low := hlo
    high := hhi
    lineerror := hlin }
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hmh

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exists_admissible_of_no_large_pencil
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D : ℕ) (δ ρ A : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F))
    (hsparse : SparseShapes shapes D)
    (hshapes : shapes.card ≤ D * Fintype.card F ^ D)
    (hL : L.card ≤ Fintype.card F)
    (hE : (overlapExcess Incidence X L : ℝ) ≤
      rigidityBudget D Incidence.savingExponent (Fintype.card F))
    (hgap : (Fintype.card F : ℝ) - L.card ≤
      rigidityBudget D Incidence.savingExponent (Fintype.card F) /
        (δ * Fintype.card F))
    (hsmall : ∀ p : ProjectivePoint F,
      ((coverPencil L p).card : ℝ) < (1 - ρ) * Fintype.card F) :
    ∃ a : LineTuple F (logarithmicSampleSize A (Fintype.card F)),
      (∀ i, a i ∈ L) ∧ AdmissibleTuple shapes D (10 * (D + 1)) a ∧
        ((X ∩ crossPoints a).card : ℝ) <
          δ * (logarithmicSampleSize A (Fintype.card F) : ℝ) ^ 2 / 2 := by
  let q : ℝ := Fintype.card F
  let κ : ℝ := Incidence.savingExponent
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one params.q_one
  have hκ : 0 ≤ κ := Incidence.savingExponent_pos.le
  have hm : q / 2 ≤ (L.card : ℝ) := by
    have hg := params.gap_half
    linarith
  have hcount : q - rigidityBudget D κ q / (δ * q) ≤ (L.card : ℝ) := by
    linarith
  have hh : 1 ≤ h := by dsimp [h]; omega
  have ht : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (hh.trans params.h_t)
  have hK : (shapes.card : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ) := by
    have hhcast : (shapes.card : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) ^ D := by
      exact_mod_cast hshapes
    simpa only [Real.rpow_natCast] using hhcast
  by_cases hlow : (maxConcurrency L : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  · have hheavy : ((heavyPoints Incidence X L (q ^ (1 / 2 - κ / 3))).card : ℝ) ≤
        q ^ (1 + κ) :=
      (heavyPoints_card_le_of_excess X L _ _ params.T_one hE).trans params.heavy
    have hpair := orderedPairMass_le_of_uniform_incidence hq hsub X L
      (q ^ (1 / 2 - κ / 3)) (maxConcurrency L)
      (Real.rpow_nonneg hqpos.le _) (Nat.cast_nonneg _) hheavy hL
      (fun p => Nat.cast_le.mpr (coverPencil_card_le_maxConcurrency L p))
    have hratio := rigidity_pair_ratio_le D params.q_one hκ hm hlow hE hpair
    have hm4 : 4 ≤ L.card := by exact_mod_cast params.m_four.trans hm
    have hmH : 4 * h ≤ L.card := by exact_mod_cast params.m_h.trans hm
    have hmT : 2 * t ≤ L.card := by exact_mod_cast params.m_t.trans hm
    have hfailure : lowFailureBound X L shapes D (maxConcurrency L) h t δ < 1 := by
      have hbound := low_sampling_failure_le_envelope (A := A) D L.card (maxConcurrency L)
        shapes.card hqpos hδ hm hm4 hmH
        (Nat.cast_nonneg (orderedPairMass Incidence X L)) hlow hK hratio
      exact (show lowFailureBound X L shapes D (maxConcurrency L) h t δ ≤
        lowFailureEnvelope D δ A κ q from hbound).trans_lt params.low
    exact exists_low_sample_of_failureBound_lt_one X L shapes D (maxConcurrency L)
      h t δ hδ ht hmT (by omega) hsparse
      (coverPencil_card_le_maxConcurrency L) hfailure
  · let p := maxCenter L
    have hR : q ^ (1 / 2 + κ / 4) ≤ ((coverPencil L p).card : ℝ) :=
      (lt_of_not_ge hlow).le
    have hN : ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) :=
      complement_card_ge_half_of_no_large_pencil L q ρ
        (rigidityBudget D κ q) δ hcount params.gap_rho hsmall p
    have htR : t ≤ (coverPencil L p).card := by exact_mod_cast params.r_t.trans hR
    have htN : t ≤ (L \ coverPencil L p).card := by exact_mod_cast params.n_t.trans hN
    have hhR : 2 * h ≤ (coverPencil L p).card := by exact_mod_cast params.r_h.trans hR
    have hhN : 2 * h ≤ (L \ coverPencil L p).card := by exact_mod_cast params.n_h.trans hN
    have hfailure : highFailureBound X L p shapes D h t δ < 1 := by
      have hbound := high_sampling_failure_le_envelope (A := A) D (coverPencil L p).card
        (L \ coverPencil L p).card shapes.card hqpos hδ hρ
        (Nat.cast_nonneg (overlapExcess Incidence X L))
        (hE.trans (rigidityBudget_le D hκ params.q_one)) hR hN hhR hhN hK
      exact (show highFailureBound X L p shapes D h t δ ≤
        highFailureEnvelope D δ ρ A κ q from hbound).trans_lt params.high
    exact highConcurrency_exists_admissible X L p shapes D h t δ hsparse hδ
      hh params.h_t htR htN hfailure

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {D : ℕ} {δ ρ A : ℝ}

theorem goodLineCover_of_goodCounts_goodTuples
    (process : DeletionProcess F D δ) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F))
    (ω : process.Config)
    (hcounts : GoodCounts process (Incidence.savingExponent / 10) ω)
    (htuples : GoodTuples process (10 * (D + 1))
      (logarithmicSampleSize A (Fintype.card F)) ω) :
    GoodLineCover δ ρ ω := by
  let q : ℝ := Fintype.card F
  let κ : ℝ := Incidence.savingExponent
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one params.q_one
  have hτ : δ * q ≤ process.survival * q :=
    mul_le_mul_of_nonneg_right process.survivalLower hqpos.le
  refine ⟨?_, ?_⟩
  · intro l
    have hl := (hcounts.2 l).1
    have herr := params.lineerror
    change δ * q / 2 ≤ retainedCount {linePoints l} (linePoints l) ω
    linarith
  · intro L hL hmiss
    by_contra hnone
    have hsmall (p : ProjectivePoint F) :
        ((coverPencil L p).card : ℝ) < (1 - ρ) * q :=
      lt_of_not_ge (fun hp => hnone ⟨p, hp⟩)
    let K := cleanLines ω L
    have hK : K.card ≤ Fintype.card F :=
      (Finset.card_le_card (cleanLines_subset ω L)).trans hL
    have hsmallK (p : ProjectivePoint F) :
        ((coverPencil K p).card : ℝ) < (1 - ρ) * q :=
      (Nat.cast_le.mpr (Finset.card_le_card
        (coverPencil_mono (cleanLines_subset ω L) p))).trans_lt (hsmall p)
    have htotal : process.survival * q ^ 2 - q ^ (3 / 2 + κ / 10) ≤
        ((survivors ∅ ω).card : ℝ) := by
      have h := (abs_le.mp hcounts.1).1
      linarith
    have hlines (l : AffineLine F) :
        ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ) ≤
          process.survival * q + ((D : ℝ) + q ^ (1 / 2 + κ / 10)) := by
      have h := (hcounts.2 l).2
      change retainedCount {linePoints l} (linePoints l) ω ≤ _
      linarith
    have hmissR : ((survivors ∅ ω \ L.biUnion linePoints).card : ℝ) ≤ 2 * q := by
      dsimp only [q]
      exact_mod_cast hmiss
    have hb := clean_cover_count_bounds ω L process.survival δ
      (q ^ (3 / 2 + κ / 10)) ((D : ℝ) + q ^ (1 / 2 + κ / 10)) (2 * q)
      hδ process.survivalLower (by positivity) htotal hlines hmissR hL
    have hbudget := rigidityBudget_eq_errors D (κ := κ) hqpos
    rw [← hbudget] at hb
    obtain ⟨a, haK, ha, hfew⟩ := exists_admissible_of_no_large_pencil
      (survivors ∅ ω) K process.shapes D δ ρ A hδ hρ hq hsub params
      process.sparse process.shapeCount hK hb.1 hb.2 hsmallK
    exact htuples.no_sparse_clean_tuple L a ha haK hfew

end RyserCoveringCounterexample.LineCover

end

end OAI
end

section
namespace OAI

open Filter Topology
open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

universe u

def linecoverFailureBound (D : ℕ) (δ A q : ℝ) : ℝ :=
  2 * (1 + q * (q + 1)) *
      Real.exp (-q ^ (2 * (Incidence.savingExponent / 10)) / (16 * (D : ℝ) ^ 5)) +
    2 * (q * (q + 1)) ^ (2 * logarithmicSampleSize A q) *
      Real.exp (-tupleTailConstant D (10 * (D + 1)) δ *
        (logarithmicSampleSize A q : ℝ) ^ 2)

theorem prob_not_goodLineCover_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {D : ℕ} {δ ρ A : ℝ} (process : DeletionProcess F D δ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (params : RigidityParameters D δ ρ A Incidence.savingExponent (Fintype.card F)) :
    process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      linecoverFailureBound D δ A (Fintype.card F) := by
  let h := 10 * (D + 1)
  let t := logarithmicSampleSize A (Fintype.card F)
  have hh : 0 < h := by dsimp [h]; omega
  have ht : 0 < t := lt_of_lt_of_le hh params.h_t
  have hε : 0 < Incidence.savingExponent / 10 := by
    exact div_pos Incidence.savingExponent_pos (by norm_num)
  have hεhalf : Incidence.savingExponent / 10 ≤ 1 / 2 := by
    linarith [Incidence.savingExponent_lt_tenth]
  have hcounts := process.prob_not_goodCounts (Incidence.savingExponent / 10)
    (by omega : 1 ≤ D) hε hεhalf
  have htuples := process.prob_not_goodTuples h t hD hh ht hδ
  have hbad : process.law.prob (fun ω => ¬ GoodLineCover δ ρ ω) ≤
      process.law.prob (fun ω =>
        ¬ GoodCounts process (Incidence.savingExponent / 10) ω ∨
        ¬ GoodTuples process h t ω) := by
    apply process.law.prob_mono
    intro ω hnot
    by_cases hc : GoodCounts process (Incidence.savingExponent / 10) ω
    · right
      intro htup
      exact hnot (goodLineCover_of_goodCounts_goodTuples process hδ hρ hq hsub
        params ω hc htup)
    · exact Or.inl hc
  exact hbad.trans ((process.law.prob_union_le _ _).trans (add_le_add hcounts htuples))

theorem tendsto_linecoverFailureBound (D : ℕ) {δ A : ℝ}
    (hD : 0 < D) (hδ : 0 < δ)
    (hA : 5 / tupleTailConstant D (10 * (D + 1)) δ < A) :
    Tendsto (linecoverFailureBound D δ A) atTop (𝓝 0) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hc0 := tupleTailConstant_pos hD
    (show 0 < 10 * (D + 1) by omega) hδ
  have hc := tendsto_count_failure_atTop hDr
    (show 0 < Incidence.savingExponent / 10 from
      div_pos Incidence.savingExponent_pos (by norm_num))
  have ht := tendsto_tuple_failure_atTop hc0 hA
  unfold linecoverFailureBound
  simpa only [add_zero] using hc.add ht

theorem uniform_linecover_probability (D : ℕ) (δ ρ : ℝ)
    (hD : 0 < D) (hδ : 0 < δ) (hρ : 0 < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
      ∀ process : DeletionProcess F D δ,
        1 - η ≤ process.law.prob (GoodLineCover δ ρ) := by
  let c0 := tupleTailConstant D (10 * (D + 1)) δ
  have hc0 : 0 < c0 := tupleTailConstant_pos hD (by omega) hδ
  let A := 6 / c0
  have hA : 0 < A := div_pos (by norm_num) hc0
  have hA5 : 5 / c0 < A := div_lt_div_of_pos_right (by norm_num) hc0
  have hnumeric := eventually_rigidityParameters D hδ hρ hA
    Incidence.savingExponent_pos Incidence.savingExponent_lt_tenth.le
  have hfailure : ∀ᶠ q : ℝ in atTop, linecoverFailureBound D δ A q ≤ η :=
    (tendsto_linecoverFailureBound D hD hδ hA5).eventually_le_const hη
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (hnumeric.and hfailure)
  refine ⟨max ⌈R⌉₊ Incidence.incidenceThreshold, ?_⟩
  intro F instField instFintype instDecidable hQ hsub process
  have hRcard : R ≤ (Fintype.card F : ℝ) :=
    (Nat.le_ceil R).trans (by
      exact_mod_cast (le_max_left ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ)
  have hq : Incidence.incidenceThreshold ≤ Fintype.card F :=
    (le_max_right ⌈R⌉₊ Incidence.incidenceThreshold).trans hQ
  obtain ⟨params, hbound⟩ := hR (Fintype.card F) hRcard
  have hprob := (prob_not_goodLineCover_le process hD hδ hρ hq hsub params).trans hbound
  rw [process.law.prob_compl] at hprob
  linarith

end RyserCoveringCounterexample.LineCover

end

end OAI
end

theorem solution.{u} : type_of% @OAI.RyserCoveringCounterexample.LineCover.uniform_linecover_probability.{u} := @OAI.RyserCoveringCounterexample.LineCover.uniform_linecover_probability.{u}
