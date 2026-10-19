-- Prove2me | solution 1 for OAI.SpinAngle.TypeAngle.one_sided_type_angle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:43:43.502845+00:00
-- url     : https://prove2.me/submissions/7f54f4ef-7ba9-486c-9d33-63d80a25871b

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/TypeAngle.lean:L192-L240
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.SpinAngle.TypeAngle.one_sided_type_angle.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_SpinAngle_TypeAngle_one_sided_type_angle) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_TypeAngle
import Theorems.Thm_OAI_SpinAngle_TypeAngle_nonempty_columns

-- ---- from OAI.RepresentationTheory.SpinAngle.Core ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
end TensorProduct
end Lean433TensorProductCompatibility

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace SpinAngle.Specht

variable {G : Type*} [contextInstance10_21 : Group G]
variable {E : Type*} [contextInstance11_21 : NormedAddCommGroup E] [contextInstance11_44 : InnerProductSpace ℂ E]

variable [contextInstance32_9 : FiniteDimensional ℂ E]

end SpinAngle.Specht

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance135_23 : Fintype ι] [contextInstance135_35 : DecidableEq ι] [contextInstance135_51 : Fintype n] [contextInstance135_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.Specht
open scoped Classical
variable {G : Type*} [contextInstance243_21 : Group G]
namespace PermutationSpace
open scoped Classical

variable {X : Type*} [contextInstance247_21 : Fintype X] [contextInstance247_33 : MulAction G X]

variable {H : Type*} [contextInstance278_21 : Group H] [contextInstance278_31 : Fintype H]

end PermutationSpace
variable {α : Type*} [contextInstance389_21 : Fintype α]

end SpinAngle.Specht

namespace SpinAngle.Young

lemma card_row_subtype (D : YoungDiagram) (i : ℕ) :
    Fintype.card {x : Cells D // x.val.1 = i} = D.rowLen i := by
  let e : {x : Cells D // x.val.1 = i} ≃ Fin (D.rowLen i) := {
    toFun := fun x => ⟨x.val.val.2, YoungDiagram.mem_iff_lt_rowLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun j => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.symm rfl
    right_inv := by intro j; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma rowRankSum_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y) :
    ∑ x : Cells D, x.val.1 ≤ ∑ x : Cells D, r x := by
  obtain ⟨σ, -, hσ⟩ := column_sort_le D r hinj
  rw [← Equiv.sum_comp σ r]
  exact Finset.sum_le_sum fun x _ => hσ x

end SpinAngle.Young

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι n : Type*} [contextInstance532_23 : Fintype ι] [contextInstance532_35 : DecidableEq ι] [contextInstance532_51 : Fintype n] [contextInstance532_63 : DecidableEq n]

variable (D : YoungDiagram) (q : ℕ)
variable (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.Specht.PermutationSpace
open scoped Classical
variable {G H X : Type*} [contextInstance635_25 : Group G] [contextInstance635_35 : Group H] [contextInstance635_45 : Fintype H] [contextInstance635_57 : Fintype X] [contextInstance635_69 : MulAction G X]
end SpinAngle.Specht.PermutationSpace

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι : Type*} [contextInstance741_21 : Fintype ι] [contextInstance741_33 : DecidableEq ι] {q : ℕ}

variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.TensorRep
open scoped Classical
variable {ι κ n : Type*} [contextInstance868_25 : Fintype ι] [contextInstance868_37 : DecidableEq ι] [contextInstance868_53 : Fintype κ] [contextInstance868_65 : DecidableEq κ]
  [contextInstance869_2 : Fintype n] [contextInstance869_14 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.TensorRep
open SpinAngle.Specht
variable {ι n : Type*} [contextInstance980_23 : Fintype ι] [contextInstance980_35 : DecidableEq ι] [contextInstance980_51 : Fintype n] [contextInstance980_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped Matrix ComplexOrder
namespace SpinAngle.SortedSpectrum
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.IsHermitian)

end SpinAngle.SortedSpectrum

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix InnerProductSpace
open SpinAngle.Specht SpinAngle.Young Module
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace BigOperators
namespace SpinAngle.ExternalTensor
open Module
variable {E F : Type*} [contextInstance1195_23 : NormedAddCommGroup E] [contextInstance1195_46 : InnerProductSpace ℂ E]
  [contextInstance1196_2 : NormedAddCommGroup F] [contextInstance1196_25 : InnerProductSpace ℂ F]
  [contextInstance1197_2 : FiniteDimensional ℂ E] [contextInstance1197_26 : FiniteDimensional ℂ F]
variable {G H : Type*} [contextInstance1198_23 : Group G] [contextInstance1198_33 : Group H]

end SpinAngle.ExternalTensor

noncomputable section
open scoped BigOperators ComplexConjugate
namespace SpinAngle.TorusNaturality
open Module
variable {n X Y E F : Type*} [contextInstance1400_29 : Fintype n] [contextInstance1400_41 : Fintype X] [contextInstance1400_53 : Fintype Y]
  [contextInstance1401_2 : AddCommGroup E] [contextInstance1401_19 : Module ℂ E] [contextInstance1401_32 : AddCommGroup F] [contextInstance1401_49 : Module ℂ F]
variable (b : Basis X ℂ E) (c : Basis Y ℂ F)
  (w : X → n → ℕ) (v : Y → n → ℕ)
  (D : (n → ℂ) → E →ₗ[ℂ] E) (D' : (n → ℂ) → F →ₗ[ℂ] F)
  (hb : ∀ a x, D a (b x) = (∏ j, a j ^ w x j) • b x)
  (hc : ∀ a y, D' a (c y) = (∏ j, a j ^ v y j) • c y)

end SpinAngle.TorusNaturality

namespace SpinAngle.SignedTensor
open scoped Classical Matrix TensorProduct InnerProductSpace
open Module
variable {q : ℕ}
variable {ι κ τ : Type*} [contextInstance1517_25 : Fintype ι] [contextInstance1517_37 : DecidableEq ι] [contextInstance1517_53 : Fintype κ] [contextInstance1517_65 : DecidableEq κ]
  [contextInstance1518_2 : Fintype τ] [contextInstance1518_14 : DecidableEq τ]

end SpinAngle.SignedTensor

noncomputable section
open scoped InnerProductSpace
namespace SpinAngle.UnitaryNaturality
variable {G : Type*} [contextInstance1640_21 : Group G]
variable {E F : Type*} [contextInstance1641_23 : NormedAddCommGroup E] [contextInstance1641_46 : InnerProductSpace ℂ E]
  [contextInstance1642_2 : NormedAddCommGroup F] [contextInstance1642_25 : InnerProductSpace ℂ F]
  [contextInstance1643_2 : FiniteDimensional ℂ E] [contextInstance1643_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
  (hσ : ∀ g x y, ⟪σ g x,σ g y⟫_ℂ = ⟪x,y⟫_ℂ)

end SpinAngle.UnitaryNaturality

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

variable {τ : Type*} [contextInstance1741_21 : Fintype τ] [contextInstance1741_33 : DecidableEq τ]

end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance1770_23 : Fintype ι] [contextInstance1770_35 : DecidableEq ι] [contextInstance1770_51 : Fintype n] [contextInstance1770_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)
end SpinAngle.PolynomialCarrier

namespace SpinAngle.ExternalTensor
open scoped TensorProduct
variable {G H : Type*} [contextInstance1802_23 : Group G] [contextInstance1802_33 : Group H] [contextInstance1802_43 : TopologicalSpace G] [contextInstance1802_64 : TopologicalSpace H]
variable {E F : Type*} [contextInstance1803_23 : NormedAddCommGroup E] [contextInstance1803_46 : InnerProductSpace ℂ E]
  [contextInstance1804_2 : NormedAddCommGroup F] [contextInstance1804_25 : InnerProductSpace ℂ F]
  [contextInstance1805_2 : FiniteDimensional ℂ E] [contextInstance1805_26 : FiniteDimensional ℂ F]
end SpinAngle.ExternalTensor

namespace SpinAngle.SignedTensor
variable {q : ℕ} {τ : Type*} [contextInstance1828_29 : Fintype τ] [contextInstance1828_41 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance1859_23 : Fintype ι] [contextInstance1859_35 : DecidableEq ι] [contextInstance1859_51 : Fintype n] [contextInstance1859_63 : DecidableEq n]
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical InnerProductSpace
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma card_rowColor (j : Fin q) :
    (Finset.univ.filter fun i : Cells D => rowColor D q hq i = j).card = D.rowLen j := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {i : Cells D // rowColor D q hq i = j} = Fintype.card {i : Cells D // i.val.1 = j.val} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun i => Fin.ext_iff))
    _ = D.rowLen j := card_row_subtype D j

include hq in
lemma sum_rowLen_eq_card : ∑ j : Fin q, D.rowLen j = Fintype.card (Cells D) := by
  have h := Finset.sum_fiberwise Finset.univ (rowColor D q hq) (fun _ : Cells D => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_rowColor, Finset.card_univ] at h
  exact_mod_cast h

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
namespace SpinAngle.TensorPositive
variable {E F : Type*} [contextInstance1947_23 : NormedAddCommGroup E] [contextInstance1947_46 : InnerProductSpace ℂ E]
  [contextInstance1948_2 : NormedAddCommGroup F] [contextInstance1948_25 : InnerProductSpace ℂ F]
  [contextInstance1949_2 : FiniteDimensional ℂ E] [contextInstance1949_26 : FiniteDimensional ℂ F]

end SpinAngle.TensorPositive

noncomputable section
open scoped BigOperators
namespace SpinAngle.EntropyMonomial
variable {ι : Type*} [contextInstance2001_21 : Fintype ι]

end SpinAngle.EntropyMonomial

noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators
namespace SpinAngle.PositiveTrace
variable {E : Type*} [contextInstance2090_21 : NormedAddCommGroup E] [contextInstance2090_44 : InnerProductSpace ℂ E]
  [contextInstance2091_2 : FiniteDimensional ℂ E]

end SpinAngle.PositiveTrace

noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder
namespace SpinAngle.Isotypic
variable {G : Type*} [contextInstance2131_21 : Group G]
variable {E F : Type*} [contextInstance2132_23 : NormedAddCommGroup E] [contextInstance2132_46 : InnerProductSpace ℂ E]
  [contextInstance2133_2 : NormedAddCommGroup F] [contextInstance2133_25 : InnerProductSpace ℂ F]
  [contextInstance2134_2 : FiniteDimensional ℂ E] [contextInstance2134_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)

end SpinAngle.Isotypic

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

include ha hb in
lemma sum_parts : ∑ i, parts a b q i = Fintype.card (Cells a) + Fintype.card (Cells b) := by
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin q, a.rowLen i) + (∑ i : Fin q, b.rowLen i) = _
  rw [PolynomialCarrier.sum_rowLen_eq_card a q ha, PolynomialCarrier.sum_rowLen_eq_card b q hb]

end SpinAngle.SignedCarrier

namespace SpinAngle.EntropyMonomial
open scoped BigOperators
variable {ι : Type*} [contextInstance2379_21 : Fintype ι] [contextInstance2379_33 : Nonempty ι]

end SpinAngle.EntropyMonomial

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance2407_21 : Fintype τ] [contextInstance2407_33 : DecidableEq τ]

end SpinAngle.SignedCarrier

noncomputable section
open scoped BigOperators
namespace SpinAngle.DenseLU

lemma border_eq {n : ℕ} (A : Mat (n+1)) :
    border (A 0 0) (fun j => A 0 j.succ) (fun i => A i.succ 0)
      (fun i j => A i.succ j.succ) = A := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> rfl

lemma continuous_border {X : Type*} [TopologicalSpace X] {n : ℕ}
    {a : X → ℂ} {b c : X → Fin n → ℂ} {D : X → Mat n}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hD : Continuous D) :
    Continuous (fun x => border (a x) (b x) (c x) (D x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact ha
  · exact (continuous_apply j).comp hb
  · exact (continuous_apply i).comp hc
  · exact (continuous_apply j).comp ((continuous_apply i).comp hD)

lemma border_factor {n : ℕ} (a : ℂ) (ha : a ≠ 0) (b c : Fin n → ℂ) (L U : Mat n) :
    border 1 0 (fun i => c i / a) L * border a b 0 U =
      border a b c (L * U + (Matrix.of fun i j => c i / a * b j)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

lemma lower_border {n : ℕ} (c : Fin n → ℂ) (L : Mat n) (hL : LowerUnipotent L) :
    LowerUnipotent (border 1 0 c L) := by
  constructor
  · intro i j hij
    change i < j at hij
    induction i using Fin.cases <;> induction j using Fin.cases
    · simp at hij
    · rfl
    · simp at hij
    · exact hL.1 (by simpa using hij)
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact hL.2 i

lemma upper_border {n : ℕ} (a : ℂ) (b : Fin n → ℂ) (U : Mat n) (hU : U.IsUpperTriangular) :
    (border a b 0 U).IsUpperTriangular := by
  intro i j hij
  induction i using Fin.cases <;> induction j using Fin.cases
  · simp at hij
  · simp at hij
  · rfl
  · exact hU (by simpa using hij)

lemma border_mem_bigCell {n : ℕ} (a : ℂ) (ha : a ≠ 0) (b c : Fin n → ℂ) (S : Mat n)
    (hS : S ∈ bigCell n) :
    border a b c (S + (Matrix.of fun i j => c i / a * b j)) ∈ bigCell (n+1) := by
  obtain ⟨L,U,hL,hU,rfl⟩ := hS
  exact ⟨border 1 0 (fun i => c i / a) L, border a b 0 U,
    lower_border _ _ hL, upper_border _ _ _ hU, (border_factor a ha b c L U).symm⟩

theorem dense_bigCell (n : ℕ) : Dense (bigCell n) := by
  induction n with
  | zero =>
    intro A
    apply subset_closure
    refine ⟨1,1,?_,?_,?_⟩
    · refine ⟨?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · exact Subsingleton.elim _ _
  | succ n ih =>
    have hpivot (a : ℂ) (ha : a ≠ 0) (b c : Fin n → ℂ) (D : Mat n) :
        border a b c D ∈ closure (bigCell (n+1)) := by
      let X : Mat n := fun i j => c i / a * b j
      have hf : Continuous (fun S : Mat n => border a b c (S + X)) :=
        continuous_border continuous_const continuous_const continuous_const
          (continuous_id.add continuous_const)
      have hh := map_mem_closure hf (ih (D-X))
        (fun S hS => border_mem_bigCell a ha b c S hS)
      change border a b c (D - X + X) ∈ closure (bigCell (n+1)) at hh
      simpa only [sub_add_cancel] using hh
    intro A
    let b : Fin n → ℂ := fun j => A 0 j.succ
    let c : Fin n → ℂ := fun i => A i.succ 0
    let D : Mat n := fun i j => A i.succ j.succ
    have hf : Continuous (fun a : ℂ => border a b c D) :=
      continuous_border continuous_id continuous_const continuous_const continuous_const
    have hh := map_mem_closure hf ((dense_compl_singleton (0 : ℂ)) (A 0 0))
      (fun a ha => hpivot a (by simpa using ha) b c D)
    simpa only [closure_closure, b, c, D, border_eq] using hh

end SpinAngle.DenseLU

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma action_mem_alternating (A : Matrix (Fin q) (Fin q) ℂ)
    (v : TensorSpace D q) (hv : v ∈ alternating D q) :
    TensorRep.action A v ∈ alternating D q := by
  intro g
  rw [← action_site_commute, hv g, map_smul]

lemma upper_weight_support (U : Matrix (Fin q) (Fin q) ℂ) (hU : U.IsUpperTriangular)
    (x : Cells D → Fin q) (hx : TensorRep.action U (highest D q hq) x ≠ 0) :
    ∑ i, (x i).val = ∑ i : Cells D, i.val.1 := by
  have hl := rowRankSum_le D (fun i => (x i).val)
    (alternating_injective D q _ (action_mem_alternating D q U _ (highest_mem D q hq)) x hx)
  apply le_antisymm _ hl
  change (∑ y, (∏ i, U (x i) (y i)) * highest D q hq y) ≠ 0 at hx
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hyv : highest D q hq y ≠ 0 := (mul_ne_zero_iff.mp hy).2
  have hp : ∀ i, x i ≤ y i := by
    intro i
    by_contra hi
    have hz : U (x i) (y i) = 0 := hU (lt_of_not_ge hi)
    exact (mul_ne_zero_iff.mp hy).1 (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  rw [← weight_eigen_support D q hq _ (highest_weight_eigen D q hq) y hyv]
  exact Finset.sum_le_sum fun i _ => hp i

lemma upper_highest (U : Matrix (Fin q) (Fin q) ℂ) (hU : U.IsUpperTriangular) :
    TensorRep.action U (highest D q hq) =
      (TensorRep.action U (highest D q hq) (rowColor D q hq)) • highest D q hq := by
  ext x
  change _ = _ * highest D q hq x
  by_cases hw : ∑ i, (x i).val = ∑ i : Cells D, i.val.1
  · exact alternating_minimal_weight D q hq _
      (action_mem_alternating D q U _ (highest_mem D q hq)) x hw
  · have hv0 : TensorRep.action U (highest D q hq) x = 0 := by
      by_contra hn
      exact hw (upper_weight_support D q hq U hU x hn)
    have he0 : highest D q hq x = 0 := by
      by_contra hn
      exact hw (weight_eigen_support D q hq _ (highest_weight_eigen D q hq) x hn)
    rw [hv0, he0, mul_zero]

lemma continuous_action_highest :
    Continuous (fun A : Matrix (Fin q) (Fin q) ℂ => TensorRep.action A (highest D q hq)) := by
  change Continuous (fun A : Matrix (Fin q) (Fin q) ℂ =>
    WithLp.toLp 2 (fun x : Cells D → Fin q => ∑ y, (∏ i, A (x i) (y i)) * highest D q hq y))
  apply (PiLp.continuous_toLp 2 (fun _ : Cells D → Fin q => ℂ)).comp
  fun_prop

lemma action_highest_mem_of_lower (S : Submodule ℂ (TensorSpace D q))
    (hS : ∀ L : Matrix (Fin q) (Fin q) ℂ, DenseLU.LowerUnipotent L →
      TensorRep.action L (highest D q hq) ∈ S)
    (A : Matrix (Fin q) (Fin q) ℂ) : TensorRep.action A (highest D q hq) ∈ S := by
  have hsub : DenseLU.bigCell q ⊆
      (fun B : Matrix (Fin q) (Fin q) ℂ => TensorRep.action B (highest D q hq)) ⁻¹'
        (S : Set (TensorSpace D q)) := by
    intro B hB
    obtain ⟨L,U,hL,hU,rfl⟩ := hB
    change TensorRep.action (L * U) (highest D q hq) ∈ S
    rw [map_mul, Module.End.mul_apply, upper_highest D q hq U hU, map_smul]
    exact S.smul_mem _ (hS L hL)
  exact closure_minimal hsub
    (S.closed_of_finiteDimensional.preimage (continuous_action_highest D q hq))
    (DenseLU.dense_bigCell q A)

end SpinAngle.PolynomialCarrier
noncomputable section
open scoped BigOperators
namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable (σ : Type*) [contextInstance2689_21 : Fintype σ] [contextInstance2689_33 : DecidableEq σ] (p : ℕ)

theorem finrank_restrictDegree :
    Module.finrank ℂ (restrictDegree σ ℂ p) = (p+1) ^ Fintype.card σ := by
  let s : Set (σ →₀ ℕ) := {f | ∀ i, f i ≤ p}
  let : Fintype s := Fintype.ofEquiv (σ → Fin (p+1)) (boundedExponentEquiv σ p).symm
  change Module.finrank ℂ (restrictSupport ℂ s) = _
  rw [Module.finrank_eq_card_basis (basisRestrictSupport ℂ s)]
  calc
    Fintype.card s = Fintype.card (σ → Fin (p+1)) := Fintype.card_congr (boundedExponentEquiv σ p)
    _ = _ := by simp

lemma card_lowerIndex (q : ℕ) : Fintype.card (LowerIndex q) = q * (q-1) / 2 := by
  simp only [LowerIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) q, Finset.sum_range_id]

lemma twice_card_lowerIndex (q : ℕ) : 2 * Fintype.card (LowerIndex q) = q * (q-1) := by
  simp only [LowerIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) q, mul_comm, Finset.sum_range_id_mul_two]

variable {q : ℕ}
end SpinAngle.PolyDimension

namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable {σ X : Type*} [contextInstance2737_23 : Fintype σ] [contextInstance2737_35 : DecidableEq σ] [contextInstance2737_51 : Fintype X] (p : ℕ)

lemma value_mem_range
    {σ : Type*} {X : Type*}
    [Fintype σ]
    [DecidableEq σ]
    [Fintype X]
    (p : ℕ) (P : X → restrictDegree σ ℂ p) (a : σ → ℂ) :
    WithLp.toLp 2 (fun x => MvPolynomial.aeval a (P x).val) ∈
      LinearMap.range (valueTranspose p P) := by
  refine ⟨(MvPolynomial.aeval a).toLinearMap.comp (restrictDegree σ ℂ p).subtype, ?_⟩
  rfl

lemma finrank_value_range
    {σ : Type*} {X : Type*}
    [contextInstance2737_23 : Fintype σ]
    [contextInstance2737_35 : DecidableEq σ]
    [Fintype X]
    (p : ℕ) (P : X → restrictDegree σ ℂ p) :
    Module.finrank ℂ (LinearMap.range (valueTranspose p P)) ≤ (p+1)^Fintype.card σ := by
  have hh := (valueTranspose p P).finrank_range_le
  rw [Subspace.dual_finrank_eq, finrank_restrictDegree] at hh
  exact hh

end SpinAngle.PolyDimension

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young PolyDimension MvPolynomial
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma eval_lowerEntry (L : Matrix (Fin q) (Fin q) ℂ) (hL : DenseLU.LowerUnipotent L)
    (i j : Fin q) : aeval (lowerParameters q L) (lowerEntry i j) = L i j := by
  unfold lowerEntry
  split_ifs with hlt heq
  · simp [aeval_X, lowerParameters]
  · subst j; simp [hL.2 i]
  · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hlt) heq
    rw [map_zero, hL.1 hij]

lemma eval_lowerCoordinate (L : Matrix (Fin q) (Fin q) ℂ) (hL : DenseLU.LowerUnipotent L)
    (x : Cells D → Fin q) :
    aeval (lowerParameters q L) (lowerCoordinate D q hq x) =
      TensorRep.action L (highest D q hq) x := by
  simp only [lowerCoordinate, map_sum, map_mul, map_prod, eval_lowerEntry q L hL]
  change (∑ y : Cells D → Fin q, (∏ i, L (x i) (y i)) *
    aeval (lowerParameters q L) (C (highest D q hq y))) =
      ∑ y : Cells D → Fin q, (∏ i, L (x i) (y i)) * highest D q hq y
  apply Finset.sum_congr rfl
  intro y _
  simp

theorem ordinary_finrank_le :
    Module.finrank ℂ (ordinary D q hq).toSubmodule ≤
      (Fintype.card (Cells D)+1) ^ (q*(q-1)/2) := by
  let P := lowerCoordinateBounded D q hq
  let S := LinearMap.range (PolyDimension.valueTranspose (Fintype.card (Cells D)) P)
  have hL (L : Matrix (Fin q) (Fin q) ℂ) (hL : DenseLU.LowerUnipotent L) :
      TensorRep.action L (highest D q hq) ∈ S := by
    have hh := PolyDimension.value_mem_range (Fintype.card (Cells D)) P (lowerParameters q L)
    have he : WithLp.toLp 2 (fun x => aeval (lowerParameters q L) (P x).val) =
        TensorRep.action L (highest D q hq) := by
      ext x; exact eval_lowerCoordinate D q hq L hL x
    rw [he] at hh
    exact hh
  let inc : (ordinary D q hq).toSubmodule →ₗ[ℂ] TensorSpace D q :=
    (alternating D q).toSubmodule.subtype.comp (ordinary D q hq).toSubmodule.subtype
  have hcarrier (v : (alternating D q).toSubmodule)
      (hv : v ∈ (ordinary D q hq).toSubmodule) : (v : TensorSpace D q) ∈ S := by
    change v ∈ Submodule.span ℂ (Set.range fun g =>
      (alternating D q).toRepresentation g
        (⟨highest D q hq, highest_mem D q hq⟩ : (alternating D q).toSubmodule)) at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g,rfl⟩ := hv
      exact action_highest_mem_of_lower D q hq S hL g.val
    | zero => exact S.zero_mem
    | add x y hx hy ihx ihy => exact S.add_mem ihx ihy
    | smul a x hx ih => exact S.smul_mem a ih
  have hinc (v : (ordinary D q hq).toSubmodule) : inc v ∈ S := hcarrier v.val v.property
  let f : (ordinary D q hq).toSubmodule →ₗ[ℂ] S := LinearMap.codRestrict S inc hinc
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : S => v.val) he
  have hh := LinearMap.finrank_le_finrank_of_injective hf
  exact hh.trans (by
    simpa only [PolyDimension.card_lowerIndex] using
      PolyDimension.finrank_value_range (Fintype.card (Cells D)) P)

end SpinAngle.PolynomialCarrier

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
namespace SpinAngle.CompactTwirl

variable {G : Type*} [contextInstance2861_21 : Group G] [contextInstance2861_31 : TopologicalSpace G] [contextInstance2861_52 : IsTopologicalGroup G]
  [contextInstance2862_2 : CompactSpace G] [contextInstance2862_19 : MeasurableSpace G] [contextInstance2862_39 : BorelSpace G]

variable {A : Type*} [contextInstance2877_21 : NormedRing A] [contextInstance2877_36 : NormedAlgebra ℝ A] [contextInstance2877_56 : CompleteSpace A]

section Positivity
variable [contextInstance2919_9 : PartialOrder A] [contextInstance2919_26 : IsOrderedAddMonoid A] [contextInstance2919_49 : StarRing A] [contextInstance2919_62 : StarOrderedRing A]
  [contextInstance2920_2 : ClosedIciTopology A] [contextInstance2920_24 : IsOrderedModule ℝ A]

end Positivity

end SpinAngle.CompactTwirl

namespace SpinAngle
open scoped Matrix.Norms.L2Operator

end SpinAngle

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance2949_21 : Group G] [contextInstance2949_31 : TopologicalSpace G] [contextInstance2949_52 : IsTopologicalGroup G]
  [contextInstance2950_2 : CompactSpace G] [contextInstance2950_19 : MeasurableSpace G] [contextInstance2950_39 : BorelSpace G]
variable {E : Type*} [contextInstance2951_21 : NormedAddCommGroup E] [contextInstance2951_44 : InnerProductSpace ℂ E]
  [contextInstance2952_2 : FiniteDimensional ℂ E]

end SpinAngle.CompactTwirl

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3008_21 : Group G] [contextInstance3008_31 : TopologicalSpace G] [contextInstance3008_52 : IsTopologicalGroup G]
  [contextInstance3009_2 : CompactSpace G] [contextInstance3009_19 : MeasurableSpace G] [contextInstance3009_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3010_23 : NormedAddCommGroup E] [contextInstance3010_46 : InnerProductSpace ℂ E]
  [contextInstance3011_2 : NormedAddCommGroup F] [contextInstance3011_25 : InnerProductSpace ℂ F]
  [contextInstance3012_2 : FiniteDimensional ℂ E] [contextInstance3012_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3043_21 : CStarAlgebra A] [contextInstance3043_38 : PartialOrder A] [contextInstance3043_55 : StarOrderedRing A]
  [contextInstance3044_2 : NonnegSpectrumClass ℝ A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3062_21 : Group G] [contextInstance3062_31 : TopologicalSpace G] [contextInstance3062_52 : IsTopologicalGroup G]
  [contextInstance3063_2 : CompactSpace G] [contextInstance3063_19 : MeasurableSpace G] [contextInstance3063_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3064_23 : NormedAddCommGroup E] [contextInstance3064_46 : InnerProductSpace ℂ E]
  [contextInstance3065_2 : NormedAddCommGroup F] [contextInstance3065_25 : InnerProductSpace ℂ F]
  [contextInstance3066_2 : FiniteDimensional ℂ E] [contextInstance3066_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

noncomputable section
open scoped BigOperators
open Set
namespace SpinAngle.CompactMixture
variable {E : Type*} [contextInstance3119_21 : NormedAddCommGroup E] [contextInstance3119_44 : NormedSpace ℝ E] [contextInstance3119_62 : FiniteDimensional ℝ E]

end SpinAngle.CompactMixture

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance3168_21 : Group G] [contextInstance3168_31 : TopologicalSpace G] [contextInstance3168_52 : IsTopologicalGroup G]
  [contextInstance3169_2 : CompactSpace G] [contextInstance3169_19 : MeasurableSpace G] [contextInstance3169_39 : BorelSpace G]
variable {E : Type*} [contextInstance3170_21 : NormedAddCommGroup E] [contextInstance3170_44 : InnerProductSpace ℂ E]
  [contextInstance3171_2 : FiniteDimensional ℂ E]

end SpinAngle.CompactTwirl

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

lemma dimension_eq : dimension a b q ha hb =
    Module.finrank ℂ (PolynomialCarrier.Carrier a q ha) *
      Module.finrank ℂ (PolynomialCarrier.Carrier b q hb) :=
  Module.finrank_tensorProduct

lemma dimension_pos : 0 < dimension a b q ha hb := by
  have : Nontrivial (Carrier a b q ha hb) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Group q))
    (rep a b q ha hb).asModule
  exact Module.finrank_pos

theorem dimension_le : dimension a b q ha hb ≤
    (Fintype.card (Cells a) + Fintype.card (Cells b) + 1) ^ (q * (q-1)) := by
  rw [dimension_eq]
  let p := Fintype.card (Cells a) + Fintype.card (Cells b) + 1
  have hA : Module.finrank ℂ (PolynomialCarrier.Carrier a q ha) ≤ p ^ (q*(q-1)/2) :=
    (PolynomialCarrier.ordinary_finrank_le a q ha).trans (Nat.pow_le_pow_left (by dsimp [p]; omega) _)
  have hB : Module.finrank ℂ (PolynomialCarrier.Carrier b q hb) ≤ p ^ (q*(q-1)/2) :=
    (PolynomialCarrier.ordinary_finrank_le b q hb).trans (Nat.pow_le_pow_left (by dsimp [p]; omega) _)
  apply (Nat.mul_le_mul hA hB).trans
  rw [← pow_add]
  have he : q*(q-1)/2 + q*(q-1)/2 = q*(q-1) := by
    have hh := PolyDimension.twice_card_lowerIndex q
    rw [PolyDimension.card_lowerIndex] at hh
    omega
  rw [he]

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

variable {τ : Type*} [contextInstance3254_21 : Fintype τ] [contextInstance3254_33 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
variable [contextInstance3273_9 : Nonempty (Fin q)]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3283_21 : Fintype τ] [contextInstance3283_33 : DecidableEq τ]

lemma projection_isStarProjection : IsStarProjection (typeProjection (τ := τ) a b q ha hb) :=
  isStarProjection_starProjection

variable [contextInstance3288_9 : Nonempty (Fin q)]
end SpinAngle.SignedCarrier

noncomputable section
namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3309_21 : CStarAlgebra A] [contextInstance3309_38 : PartialOrder A] [contextInstance3309_55 : StarOrderedRing A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3325_21 : Fintype n] [contextInstance3325_33 : DecidableEq n]
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3337_21 : Fintype τ] [contextInstance3337_33 : DecidableEq τ] [contextInstance3337_49 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3364_21 : Fintype n] [contextInstance3364_33 : DecidableEq n]
local notation "Φ" => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3392_21 : Fintype τ] [contextInstance3392_33 : DecidableEq τ]

lemma matrixProjection_isStarProjection : IsStarProjection (matrixProjection (τ := τ) a b q ha hb) := by
  have hp := projection_isStarProjection (τ := τ) a b q ha hb
  constructor
  · change matrixProjection a b q ha hb * matrixProjection a b q ha hb = _
    unfold matrixProjection
    rw [← map_mul, hp.isIdempotentElem.eq]
  · change star (matrixProjection a b q ha hb) = _
    unfold matrixProjection
    have hs := (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm.map_star'
      (typeProjection a b q ha hb)
    exact hs.symm.trans (congrArg (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm hp.isSelfAdjoint.star_eq)

variable [contextInstance3441_9 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
variable {J : Type*} [contextInstance3487_21 : Fintype J]

end SpinAngle.SignedTensor

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace SpinAngle.MatrixAnalysis
variable {n : Type*} [contextInstance3521_21 : Fintype n] [contextInstance3521_33 : DecidableEq n]
end SpinAngle.MatrixAnalysis

namespace SpinAngle.TensorMatrix
open SpinAngle.MatrixAnalysis
variable {ι n : Type*} [contextInstance3707_23 : Fintype ι] [contextInstance3707_35 : DecidableEq ι] [contextInstance3707_51 : Fintype n] [contextInstance3707_63 : DecidableEq n]

end SpinAngle.TensorMatrix

noncomputable section
open scoped BigOperators
namespace SpinAngle

lemma missingCellFactor_nonneg (m b : ℕ) : 0 ≤ missingCellFactor m b := by
  unfold missingCellFactor
  split_ifs <;> positivity

lemma missingCellFactor_le_exp (m b : ℕ) (hb : b ≤ m) :
    missingCellFactor m b ≤ Real.exp b := by
  unfold missingCellFactor
  split_ifs with h
  · have hk : 0 < m - b := Nat.sub_pos_of_lt h
    have hkR : (0 : ℝ) < (m - b : ℕ) := by exact_mod_cast hk
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le b) h)
    have hratio : 0 < (m : ℝ) / (m - b : ℕ) := div_pos hmR hkR
    apply (Real.log_le_iff_le_exp (pow_pos hratio _)).mp
    rw [Real.log_pow]
    calc
      (m - b : ℕ) * Real.log ((m : ℝ) / (m - b : ℕ))
        ≤ (m - b : ℕ) * ((m : ℝ) / (m - b : ℕ) - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) hkR.le
      _ = (b : ℝ) := by
        rw [mul_sub, mul_div_cancel₀ _ hkR.ne', mul_one, Nat.cast_sub hb]
        ring
  · exact Real.one_le_exp (Nat.cast_nonneg b)

theorem missingCellProduct {ι : Type*} [Fintype ι]
    (m : ℕ) (b : ι → ℕ) (hb : ∀ i, b i ≤ m) :
    missingCellProductFactor m b ≤ Real.exp (∑ i, (b i : ℝ)) := by
  unfold missingCellProductFactor
  calc
    ∏ i, missingCellFactor m (b i) ≤ ∏ i, Real.exp (b i : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => missingCellFactor_nonneg m (b i))
        (fun i _ => missingCellFactor_le_exp m (b i) (hb i))
    _ = Real.exp (∑ i, (b i : ℝ)) := (Real.exp_sum _ _).symm

end SpinAngle

namespace SpinAngle
open scoped BigOperators
variable {ι : Type*} [contextInstance3841_21 : Fintype ι] [contextInstance3841_33 : DecidableEq ι]

variable {R C : Type*} [contextInstance3877_23 : Fintype R] [contextInstance3877_35 : DecidableEq R] [contextInstance3877_51 : Fintype C] [contextInstance3877_63 : DecidableEq C]

lemma occupiedRow_card_le
    {R : Type*} {C : Type*}
    [Fintype R]
    [contextInstance3877_35 : DecidableEq R]
    [contextInstance3877_51 : Fintype C]
    [contextInstance3877_63 : DecidableEq C] (W : Finset (R × C)) (i : R) :
    (occupiedRow W i).card ≤ Fintype.card C := Finset.card_le_univ _

lemma missingInRow_le
    {R : Type*} {C : Type*}
    [Fintype R]
    [contextInstance3877_35 : DecidableEq R]
    [contextInstance3877_51 : Fintype C]
    [contextInstance3877_63 : DecidableEq C] (W : Finset (R × C)) (i : R) :
    missingInRow W i ≤ Fintype.card C := Nat.sub_le _ _

end SpinAngle

namespace SpinAngle.MatrixAnalysis
variable {n C : Type*} [contextInstance3931_23 : Fintype n] [contextInstance3931_35 : DecidableEq n] [contextInstance3931_51 : Fintype C] [contextInstance3931_63 : DecidableEq C]

end SpinAngle.MatrixAnalysis

namespace SpinAngle
open MatrixAnalysis TensorMatrix
variable {n R C : Type*} [contextInstance3979_25 : Fintype n] [contextInstance3979_37 : DecidableEq n]
  [contextInstance3980_2 : Fintype R] [contextInstance3980_14 : DecidableEq R] [contextInstance3980_30 : Fintype C] [contextInstance3980_42 : DecidableEq C] [contextInstance3980_58 : Nonempty C]

end SpinAngle

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace SpinAngle.DependentTensor
variable {ι : Type*} [contextInstance4012_21 : Fintype ι] [contextInstance4012_33 : DecidableEq ι]
variable {ν : ι → Type*} [contextInstance4013_25 : ∀ i, Fintype (ν i)] [contextInstance4013_46 : ∀ i, DecidableEq (ν i)]

lemma tensor_mul
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [contextInstance4012_33 : DecidableEq ι]
    {ν : ι → Type*}
    [contextInstance4013_25 : ∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] (A B : ∀ i, Mat (ν i)) : tensor (fun i => A i * B i) = tensor A * tensor B := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (j : ν i) => A i (x i) j * B i j (y i)))

end SpinAngle.DependentTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4107_25 : Fintype τ] [contextInstance4107_37 : DecidableEq τ] [contextInstance4107_53 : Fintype J] [contextInstance4107_65 : DecidableEq J]
  [contextInstance4108_2 : Fintype n] [contextInstance4108_14 : DecidableEq n]
variable (f : τ → J)

lemma tensor_mul (A B : ∀ j, Mat (Fiber f j → n)) :
    tensor f (fun j => A j * B j) = tensor f A * tensor f B := by
  change (DependentTensor.tensor (fun j => A j * B j)).submatrix (splitEquiv f) (splitEquiv f) = _
  rw [DependentTensor.tensor_mul]
  exact (Matrix.submatrix_mul_equiv _ _ (splitEquiv f) (splitEquiv f) (splitEquiv f)).symm

lemma tensor_star
    {τ : Type*} {J : Type*} {n : Type*}
    [Fintype τ]
    [DecidableEq τ]
    [contextInstance4107_53 : Fintype J]
    [DecidableEq J]
    [Fintype n]
    [DecidableEq n]
    (f : τ → J) (A : ∀ j, Mat (Fiber f j → n)) :
    tensor f (fun j => star (A j)) = star (tensor f A) := by
  ext x y
  simp [tensor, DependentTensor.tensor, Matrix.star_apply]

lemma tensor_projection (P : ∀ j, Mat (Fiber f j → n)) (hP : ∀ j, IsStarProjection (P j)) :
    IsStarProjection (tensor f P) := by
  constructor
  · change tensor f P * tensor f P = tensor f P
    rw [← tensor_mul]
    congr 1
    funext j
    exact (hP j).isIdempotentElem.eq
  · change star (tensor f P) = tensor f P
    rw [← tensor_star]
    congr 1
    funext j
    exact (hP j).isSelfAdjoint.star_eq

end SpinAngle.BlockTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4180_25 : Fintype τ] [contextInstance4180_37 : DecidableEq τ] [contextInstance4180_53 : Fintype J] [contextInstance4180_65 : DecidableEq J]
  [contextInstance4181_2 : Fintype n] [contextInstance4181_14 : DecidableEq n]
variable (f : τ → J)

end SpinAngle.BlockTensor

namespace SpinAngle.TensorMatrix
open MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance4214_23 : Fintype ι] [contextInstance4214_35 : DecidableEq ι] [contextInstance4214_51 : Fintype n] [contextInstance4214_63 : DecidableEq n]

end SpinAngle.TensorMatrix

namespace SpinAngle
open scoped BigOperators
variable {R C : Type*} [contextInstance4250_23 : Fintype R] [contextInstance4250_35 : DecidableEq R] [contextInstance4250_51 : Fintype C] [contextInstance4250_63 : DecidableEq C]

lemma sum_occupiedRow_card (W : Finset (R × C)) :
    ∑ i, (occupiedRow W i).card = W.card := by
  have he (i : R) : (occupiedRow W i).card = ∑ j : C, if (i,j) ∈ W then 1 else 0 := by
    simp only [occupiedRow, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [he]
  rw [← Finset.sum_product (f := fun x : R × C => if x ∈ W then (1 : ℕ) else 0)]
  simp only [Finset.univ_product_univ, ← Finset.sum_filter]
  have he : (Finset.univ.filter fun x : R × C => x ∈ W) = W := by ext x; simp
  rw [he]
  simp

lemma sum_missingInRow (W : Finset (R × C)) :
    ∑ i, missingInRow W i = Fintype.card R * Fintype.card C - W.card := by
  have he : (∑ i, missingInRow W i) + W.card = Fintype.card R * Fintype.card C := by
    rw [← sum_occupiedRow_card W, ← Finset.sum_add_distrib]
    have hi (i : R) : missingInRow W i + (occupiedRow W i).card = Fintype.card C :=
      Nat.sub_add_cancel (occupiedRow_card_le W i)
    simp [hi]
  omega

lemma boardPhi_le_exp_holes (W : Finset (R × C)) :
    missingCellProductFactor (Fintype.card C) (missingInRow W) ≤
      Real.exp (Fintype.card R * Fintype.card C - W.card : ℕ) := by
  have h := missingCellProduct (Fintype.card C) (missingInRow W) (missingInRow_le W)
  have hs : (∑ i, (missingInRow W i : ℝ)) =
      (Fintype.card R * Fintype.card C - W.card : ℕ) := by
    exact_mod_cast sum_missingInRow W
  rwa [hs] at h
end SpinAngle

namespace SpinAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young

namespace TypeLabel
variable {q : ℕ}
lemma projection_isStarProjection (D : TypeLabel q) (τ : Type*) [Fintype τ] [DecidableEq τ] :
    IsStarProjection (D.projection τ) :=
  SignedCarrier.matrixProjection_isStarProjection D.even D.odd q D.even_height D.odd_height

lemma dimension_pos (D : TypeLabel q) : 0 < D.dimension :=
  SignedCarrier.dimension_pos D.even D.odd q D.even_height D.odd_height

lemma dimension_le (D : TypeLabel q) : D.dimension ≤ (D.size + 1) ^ (q*(q-1)) :=
  SignedCarrier.dimension_le D.even D.odd q D.even_height D.odd_height

lemma entropy_eq_zero_of_size_zero (D : TypeLabel q) (hD : D.size = 0) : D.entropy = 0 := by
  have hs : ∑ i, SignedCarrier.parts D.even D.odd q i = 0 :=
    (SignedCarrier.sum_parts D.even D.odd q D.even_height D.odd_height).trans hD
  have hi : ∀ i, SignedCarrier.parts D.even D.odd q i = 0 := by
    intro i
    have h := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => Nat.zero_le (SignedCarrier.parts D.even D.odd q j)) (Finset.mem_univ i)
    rw [hs] at h
    exact Nat.eq_zero_of_le_zero h
  simp [entropy, SignedCarrier.entropy, EntropyMonomial.entropy, hi]
end TypeLabel

namespace EvenDensity
variable {q : ℕ}
variable {J : Type*} [contextInstance4345_21 : Fintype J] [contextInstance4345_33 : Nonempty J]
end EvenDensity

namespace TypeLabel
variable {q : ℕ}
variable {τ : Type*} [contextInstance4358_21 : Fintype τ] [contextInstance4358_33 : DecidableEq τ]
variable [contextInstance4367_9 : Nonempty (Fin q)]
end TypeLabel

namespace TypeBlocks
universe u
open MatrixAnalysis
variable {q : ℕ}
variable {τ : Type*} {J : Type u} [contextInstance4383_34 : Fintype τ] [contextInstance4383_46 : DecidableEq τ] [contextInstance4383_62 : Fintype J] [contextInstance4383_74 : DecidableEq J]

lemma projection_isStarProjection (f : τ → J) (D : J → TypeLabel q) :
    IsStarProjection (projection f D) :=
  BlockTensor.tensor_projection f _ (fun j => (D j).projection_isStarProjection _)

variable [contextInstance4410_9 : Nonempty (Fin q)]

end TypeBlocks
end SpinAngle

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

-- ---- from OAI.RepresentationTheory.SpinAngle.Compression ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
open scoped BigOperators
namespace SpinAngle.Analytic

variable {A : Type*} [contextInstance35_21 : CStarAlgebra A] [contextInstance35_38 : PartialOrder A] [contextInstance35_55 : StarOrderedRing A]
  [contextInstance36_2 : NonnegSpectrumClass ℝ A]

lemma norm_three_projections_sq_le_one
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] (h k p : A)
    (hh : IsStarProjection h) (hk : IsStarProjection k) (hp : IsStarProjection p) :
    ‖h * k * p‖ ^ 2 ≤ 1 := by
  have hn : ‖h * k * p‖ ≤ 1 := calc
    _ ≤ (‖h‖ * ‖k‖) * ‖p‖ := (norm_mul_le _ _).trans <|
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * 1) * 1 := mul_le_mul
      (mul_le_mul hh.norm_le hk.norm_le (norm_nonneg _) zero_le_one)
      hp.norm_le (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num
  calc
    _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = 1 := by norm_num

end SpinAngle.Analytic

end
end

end OAI

-- ---- from OAI.RepresentationTheory.SpinAngle.TypeAngle ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators

namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MatrixAnalysis TensorMatrix
variable {q : ℕ} [contextInstance30_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance31_23 : Fintype R] [contextInstance31_35 : DecidableEq R] [contextInstance31_51 : Fintype C] [contextInstance31_63 : DecidableEq C]

end SpinAngle.TypeAngle

namespace SpinAngle.TypeBlocks
open scoped BigOperators
variable {q : ℕ}
variable {τ J : Type*} [contextInstance157_23 : Fintype τ] [contextInstance157_35 : DecidableEq τ] [contextInstance157_51 : Fintype J] [contextInstance157_63 : DecidableEq J]

lemma dimension_pos {q : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (D : J → TypeLabel q) : 0 < dimension D :=
  Finset.prod_pos fun j _ => (D j).dimension_pos

lemma dimension_le {q : ℕ} {τ : Type*} {J : Type*}
    [Fintype τ] [DecidableEq τ] [Fintype J] [DecidableEq J] (f : τ → J) (D : J → TypeLabel q)
    (hsize : ∀ j, (D j).size = Fintype.card (Fiber f j)) :
    dimension D ≤ (Fintype.card τ + 1) ^ (Fintype.card J * (q*(q-1))) := by
  have h (j : J) : (D j).dimension ≤ (Fintype.card τ + 1) ^ (q*(q-1)) := by
    apply (D j).dimension_le.trans
    apply Nat.pow_le_pow_left
    rw [hsize]
    exact Nat.add_le_add_right (Fintype.card_subtype_le _) 1
  calc
    dimension D ≤ ∏ _j : J, (Fintype.card τ + 1) ^ (q*(q-1)) :=
      Finset.prod_le_prod₀ (fun j _ => Nat.zero_le _) (fun j _ => h j)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]; congr 1; exact Nat.mul_comm _ _
end SpinAngle.TypeBlocks

namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ} [contextInstance179_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance180_23 : Fintype R] [contextInstance180_35 : DecidableEq R] [contextInstance180_51 : Fintype C] [contextInstance180_63 : DecidableEq C]

theorem one_sided_type_angle (W : Finset (R × C))
    (D : TypeLabel q) (H : C → TypeLabel q) (K : R → TypeLabel q)
    (hD : D.size = W.card)
    (hH : ∀ j, (H j).size = Fintype.card (TypeBlocks.Fiber (column W) j))
    (hK : ∀ i, (K i).size = Fintype.card (TypeBlocks.Fiber (row W) i)) :
    (‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W)) ∧
    (min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy +
        (Fintype.card R * Fintype.card C - W.card : ℕ)) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ))) ∧
    TypeBlocks.dimension H * TypeBlocks.dimension K ≤
      (W.card + 1) ^ ((Fintype.card R + Fintype.card C) * q * (q-1)) := by
  classical
  have hangle : ‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) := by
    cases isEmpty_or_nonempty C with
    | inr h => exact nonempty_columns W D H K
    | inl h =>
      have hW : W = ∅ := Finset.eq_empty_of_isEmpty W
      have hd : D.entropy = 0 := D.entropy_eq_zero_of_size_zero (by simpa [hW] using hD)
      have hksize (i : R) : (K i).size = 0 := by simpa [hW] using hK i
      have hkentropy : TypeBlocks.entropy K = 0 := by
        simp only [TypeBlocks.entropy, fun i => (K i).entropy_eq_zero_of_size_zero (hksize i), Finset.sum_const_zero]
      have hphi : phi W = 1 := by simp [phi, missingCellProductFactor, missingCellFactor]
      have hdim : 1 ≤ (TypeBlocks.dimension K : ℝ) := by
        exact_mod_cast TypeBlocks.dimension_pos K
      have hnorm := Analytic.norm_three_projections_sq_le_one
        (TypeBlocks.projection (column W) H) (TypeBlocks.projection (row W) K) (D.projection W)
        (TypeBlocks.projection_isStarProjection _ _) (TypeBlocks.projection_isStarProjection _ _)
        (D.projection_isStarProjection W)
      have hhent : TypeBlocks.entropy H = 0 := by simp [TypeBlocks.entropy]
      have hhdim : TypeBlocks.dimension H = 1 := by simp [TypeBlocks.dimension]
      simpa only [hhent, hhdim, Nat.cast_one, hd, hkentropy, hphi, add_zero,
        sub_zero, Real.exp_zero, one_mul, mul_one, min_eq_left hdim] using hnorm
  refine ⟨hangle, ?_, ?_⟩
  · apply min_le_min_left
    have h := mul_le_mul_of_nonneg_left (boardPhi_le_exp_holes W)
      (mul_nonneg (mul_nonneg (Real.exp_pos (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy)).le (Nat.cast_nonneg (TypeBlocks.dimension H)))
        (Nat.cast_nonneg (TypeBlocks.dimension K)))
    convert h using 1 <;> simp only [phi, Real.exp_add] ; ring
  · have h := Nat.mul_le_mul (TypeBlocks.dimension_le (column W) H hH)
      (TypeBlocks.dimension_le (row W) K hK)
    rw [← pow_add] at h
    simpa only [Fintype.card_coe, show Fintype.card C * (q * (q-1)) + Fintype.card R * (q * (q-1)) =
        (Fintype.card R + Fintype.card C) * q * (q-1) by ring] using h
end SpinAngle.TypeAngle

end

end OAI

-- ---- mission target ----
open OAI OAI.SpinAngle OAI.SpinAngle.TypeAngle
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix TensorProduct
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ} [Nonempty (Fin q)]
variable {R C : Type*}
variable [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open MeasureTheory TopologicalSpace Set
open Set

namespace OAI
namespace SpinAngle.TypeAngle
theorem _root_.solution (W : Finset (R × C))
    (D : TypeLabel q) (H : C → TypeLabel q) (K : R → TypeLabel q)
    (hD : D.size = W.card)
    (hH : ∀ j, (H j).size = Fintype.card (TypeBlocks.Fiber (column W) j))
    (hK : ∀ i, (K i).size = Fintype.card (TypeBlocks.Fiber (row W) i)) :
    (‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W)) ∧
    (min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy +
        (Fintype.card R * Fintype.card C - W.card : ℕ)) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ))) ∧
    TypeBlocks.dimension H * TypeBlocks.dimension K ≤
      (W.card + 1) ^ ((Fintype.card R + Fintype.card C) * q * (q - 1)) := by
  first
    | exact OAI.SpinAngle.TypeAngle.one_sided_type_angle W D H K hD hH hK
    | exact OAI.SpinAngle.TypeAngle.one_sided_type_angle
    | (apply OAI.SpinAngle.TypeAngle.one_sided_type_angle <;> assumption)
    | (intros; apply OAI.SpinAngle.TypeAngle.one_sided_type_angle <;> assumption)
end SpinAngle.TypeAngle
end OAI
