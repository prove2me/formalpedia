-- Prove2me | solution 1 for OAI.SignedSweeps.sector_positive_restriction
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:10:08.154043+00:00
-- url     : https://prove2.me/submissions/c52b6592-9b14-4b57-96cd-9ca594f260d0

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

section
-- module OAI.Probability.SignedSweeps.Model
namespace TensorProduct

end TensorProduct

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma spechtRepresentation_norm {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (x : Specht lam) : ‖spechtRepresentation lam g x‖ = ‖x‖ := by
  let x' : (spechtSubrepresentation lam).toSubmodule := x
  change ‖regularIsometry g (x' : RegularSpace n)‖ = ‖(x' : RegularSpace n)‖
  exact (regularIsometry g).norm_map _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupAverage
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma representation_inner_inverse {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : E) :
    inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  let e : E →ₗᵢ[ℂ] E := ⟨ρ g, hρ g⟩
  have he : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc
    inner ℂ (ρ g x) y = inner ℂ (ρ g x) (ρ g (ρ g⁻¹ y)) := congrArg _ he.symm
    _ = inner ℂ x (ρ g⁻¹ y) := e.inner_map_map x (ρ g⁻¹ y)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SwitchGeneration
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma swap_mem_fiberSubgroup {A C : Type*} [DecidableEq A] (f : A → C)
    {x y : A} (hxy : f x = f y) : Equiv.swap x y ∈ fiberSubgroup f := by
  intro z
  by_cases hx : z = x
  · subst z; simpa using hxy.symm
  by_cases hy : z = y
  · subst z; simpa using hxy
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Invariants
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def complexSign (n : ℕ) : SymmetricGroup n →* ℂ where
  toFun g := (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ)
  map_one' := by simp
  map_mul' g h := by simp

def spechtInclusion {n : ℕ} (lam : Partition n) : Specht lam →ₗ[ℂ] RegularSpace n :=
  (spechtSubrepresentation lam).toSubmodule.subtype

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PolytabloidNonzero
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma mem_row_col_eq_one {n : ℕ} (lam : Partition n) {g : SymmetricGroup n}
    (hr : g ∈ rowSubgroup lam) (hc : g ∈ colSubgroup lam) : g = 1 := by
  apply Equiv.ext
  intro x
  change g x = x
  apply lam.tableau.symm.injective
  apply Subtype.ext
  exact Prod.ext (hr x) (hc x)

lemma column_row_product_eq_one_iff {n : ℕ} (lam : Partition n)
    (c : colSubgroup lam) (a : rowSubgroup lam) :
    c.1 * a.1 = 1 ↔ c = 1 ∧ a = 1 := by
  constructor
  · intro hca
    have hc : c.1 = a.1⁻¹ := eq_inv_of_mul_eq_one_left hca
    have hc1 : c = 1 := by
      apply Subtype.ext
      apply mem_row_col_eq_one lam
      · rw [hc]
        exact (rowSubgroup lam).inv_mem a.property
      · exact c.property
    refine ⟨hc1, ?_⟩
    rw [hc1, OneMemClass.coe_one, one_mul] at hca
    exact Subtype.ext hca
  · rintro ⟨rfl, rfl⟩
    simp

lemma polytabloid_at_one {n : ℕ} (lam : Partition n) : polytabloid lam 1 = 1 := by
  classical
  have he (c : colSubgroup lam) (a : rowSubgroup lam) :
      Pi.single (M := fun _ => ℂ) (c.1 * a.1) (1 : ℂ) (1 : SymmetricGroup n) =
        if c = 1 ∧ a = 1 then 1 else 0 := by
    simp only [Pi.single_apply, ← column_row_product_eq_one_iff lam, eq_comm]
  simp [polytabloid, he, ite_and]

lemma polytabloid_ne_zero {n : ℕ} (lam : Partition n) : polytabloid lam ≠ 0 := by
  intro h
  have hh := congrArg (fun f : RegularSpace n => f 1) h
  simp only [polytabloid_at_one, PiLp.zero_apply, one_ne_zero] at hh

def spechtGenerator {n : ℕ} (lam : Partition n) : Specht lam :=
  ⟨polytabloid lam, Submodule.subset_span ⟨1, by simp⟩⟩

lemma spechtGenerator_ne_zero {n : ℕ} (lam : Partition n) : spechtGenerator lam ≠ 0 := by
  intro h
  have hh := congrArg (spechtInclusion lam) h
  exact polytabloid_ne_zero lam hh

instance spechtNontrivial {n : ℕ} (lam : Partition n) : Nontrivial (Specht lam) :=
  ⟨⟨spechtGenerator lam, 0, spechtGenerator_ne_zero lam⟩⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ColumnAnnihilation
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma regularRepresentation_single {n : ℕ} (g h : SymmetricGroup n) (z : ℂ) :
    regularRepresentation n g (EuclideanSpace.single h z) =
      EuclideanSpace.single (g * h) z := by
  classical
  ext k
  simp only [regularRepresentation_apply, PiLp.single_apply, inv_mul_eq_iff_eq_mul]

lemma complexSign_mul_self {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g * complexSign n g = 1 := by
  change (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) = 1
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

lemma polytabloid_column_action {n : ℕ} (lam : Partition n) (g : colSubgroup lam) :
    regularRepresentation n g.1 (polytabloid lam) = complexSign n g.1 • polytabloid lam := by
  classical
  change regularRepresentation n g.1 (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
    complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1) = complexSign n g.1 •
    (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
      complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1)
  simp only [map_sum, map_smul, regularRepresentation_single, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft g)
  intro c
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, smul_smul, ← mul_assoc,
    complexSign_mul_self, one_mul]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PartitionGeometry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma polytabloid_right_row {n : ℕ} (lam : Partition n)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (g * a.1) = polytabloid lam g := by
  classical
  simp only [polytabloid, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_congr rfl
  intro c _
  symm
  apply Fintype.sum_equiv (Equiv.mulRight a)
  intro b
  have h : (g * a.1 = c.1 * (b * a).1) ↔ g = c.1 * b.1 := by
    simp only [Subgroup.coe_mul, ← mul_assoc, mul_left_inj]
  simp only [Equiv.coe_mulRight, PiLp.single_apply, h]

lemma specht_right_row {n : ℕ} (lam : Partition n) (x : Specht lam)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    (spechtInclusion lam x) (g * a.1) = (spechtInclusion lam x) g := by
  have haux : ∀ y ∈ (spechtSubrepresentation lam).toSubmodule,
      y (g * a.1) = y g := by
    intro y hy
    change y ∈ Submodule.span ℂ _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      simp only [regularRepresentation_apply, ← mul_assoc]
      exact polytabloid_right_row lam a _
    | zero => rfl
    | add y z _ _ hy hz => simpa only [PiLp.add_apply] using congrArg₂ (· + ·) hy hz
    | smul c y _ hy => simpa only [PiLp.smul_apply] using congrArg (c • ·) hy
  exact haux _ x.property

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RowSymmetry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma diagram_rowLens_sum (lam : YoungDiagram) : lam.rowLens.sum = lam.card := by
  have hh (c : ℕ × ℕ) (hc : c ∈ lam.cells) : c.1 ∈ Finset.range (lam.colLen 0) := by
    have hi : c.1 < lam.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hc
    exact Finset.mem_range.mpr (hi.trans_le (lam.colLen_anti 0 c.2 (Nat.zero_le _)))
  have he := Finset.sum_fiberwise_of_maps_to (g := Prod.fst) hh (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at he
  rw [YoungDiagram.rowLens, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, YoungDiagram.card]
  simp_rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  exact he

lemma partition_rowLens_sum {n : ℕ} (lam : Partition n) : lam.1.rowLens.sum = n :=
  (diagram_rowLens_sum lam.1).trans lam.2

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.YoungLemma
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma fin_strictMono_val_le {a : ℕ} (f : Fin a → ℕ) (hf : StrictMono f) (i : Fin a) :
    i.val ≤ f i := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < a := by omega
    have h := hf (show (⟨i, hi'⟩ : Fin a) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i)
    have := ih hi'
    change i + 1 ≤ f ⟨i + 1, hi⟩
    change i ≤ f ⟨i, hi'⟩ at this
    omega

lemma fin_injective_sum_lower {a : ℕ} (f : Fin a → ℕ) (hf : Function.Injective f) :
    (∑ i : Fin a, i.val) ≤ ∑ i : Fin a, f i := by
  let s : Finset ℕ := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∑ i : Fin a, s.orderEmbOfFin hs i = ∑ i : Fin a, f i := by
    have h₁ := Finset.sum_image (s := Finset.univ) (f := id) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.sum_image (s := Finset.univ) (f := id) hf.injOn
    simp only [id_eq, Finset.image_orderEmbOfFin_univ] at h₁ h₂
    exact h₁.symm.trans h₂
  rw [← he]
  exact Finset.sum_le_sum (fun i _ => fin_strictMono_val_le _ (s.orderEmbOfFin hs).strictMono i)

lemma fin_injective_minimal_sum {a : ℕ} (f : Fin a → ℕ) (hf : Function.Injective f)
    (hmin : ∑ i : Fin a, f i = ∑ i : Fin a, i.val) (i : Fin a) : f i < a := by
  let s : Finset ℕ := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∑ i : Fin a, s.orderEmbOfFin hs i = ∑ i : Fin a, i.val := by
    have h₁ := Finset.sum_image (s := Finset.univ) (f := id) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.sum_image (s := Finset.univ) (f := id) hf.injOn
    simp only [id_eq, Finset.image_orderEmbOfFin_univ] at h₁ h₂
    exact (h₁.symm.trans h₂).trans hmin
  have hp : ∀ j : Fin a, s.orderEmbOfFin hs j = j.val := by
    have hh := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset (Fin a))) =>
      fin_strictMono_val_le _ (s.orderEmbOfFin hs).strictMono j)).mp he.symm
    exact fun j => (hh j (Finset.mem_univ _)).symm
  have hi : f i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, hj⟩ := (s.orderIsoOfFin hs).surjective ⟨f i, hi⟩
  have h := congrArg Subtype.val hj
  change s.orderEmbOfFin hs j = f i at h
  rw [hp] at h
  exact h ▸ j.isLt

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma rowOf_lt {n : ℕ} (lam : Partition n) (x : Fin n) : lam.rowOf x < lam.1.colLen 0 := by
  have h := YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x).property
  exact h.trans_le (lam.1.colLen_anti 0 _ (Nat.zero_le _))

lemma colOf_lt_rowLen {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.colOf x < lam.1.rowLen (lam.rowOf x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (lam.tableau.symm x).property

def rowEquiv {n : ℕ} (lam : Partition n) :
    (Σ i : Fin (lam.1.colLen 0), Fin (lam.1.rowLen i)) ≃ Fin n where
  toFun x := lam.tableau ⟨(x.1.val, x.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  invFun x := ⟨⟨lam.rowOf x, lam.rowOf_lt x⟩, ⟨lam.colOf x, lam.colOf_lt_rowLen x⟩⟩
  left_inv x := by
    apply Sigma.ext
    · apply Fin.ext
      simp [rowOf]
    · apply (Fin.heq_ext_iff (by simp [rowOf])).mpr
      simp [colOf]
  right_inv x := by simp only; exact lam.tableau.apply_symm_apply x

@[simp] lemma rowOf_rowEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) (j : Fin (lam.1.rowLen i)) :
    lam.rowOf (lam.rowEquiv ⟨i, j⟩) = i.val := by simp [rowEquiv, rowOf]

@[simp] lemma colOf_rowEquiv {n : ℕ} (lam : Partition n)
    (i : Fin (lam.1.colLen 0)) (j : Fin (lam.1.rowLen i)) :
    lam.colOf (lam.rowEquiv ⟨i, j⟩) = j.val := by simp [rowEquiv, colOf]

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma young_column_bound {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (x : Fin n) : lam.colOf (g x) < lam.1.rowLen (lam.rowOf x) := by
  let f := fun i : Fin (lam.1.colLen 0) => fun j : Fin (lam.1.rowLen i) =>
    lam.colOf (g (lam.rowEquiv ⟨i, j⟩))
  have hf (i : Fin (lam.1.colLen 0)) : Function.Injective (f i) := by
    intro j k h
    have he := htrans (lam.rowEquiv ⟨i, j⟩) (lam.rowEquiv ⟨i, k⟩) (by simp) h
    have hsig := lam.rowEquiv.injective he
    exact Sigma.mk.inj_iff.mp hsig |>.2 |> eq_of_heq
  have hsum : ∑ i, ∑ j, f i j = ∑ i : Fin (lam.1.colLen 0), ∑ j : Fin (lam.1.rowLen i), j.val := by
    calc
      _ = ∑ y : Fin n, lam.colOf (g y) := by
        exact (Fintype.sum_sigma (fun t : Σ i : Fin (lam.1.colLen 0),
          Fin (lam.1.rowLen i) => lam.colOf (g (lam.rowEquiv t)))).symm.trans
            (Equiv.sum_comp lam.rowEquiv (fun y : Fin n => lam.colOf (g y)))
      _ = ∑ y : Fin n, lam.colOf y := Equiv.sum_comp g _
      _ = _ := by
        rw [← Equiv.sum_comp lam.rowEquiv lam.colOf, Fintype.sum_sigma]
        simp only [Partition.colOf_rowEquiv]
  have hrow (i : Fin (lam.1.colLen 0)) : ∑ j, f i j = ∑ j : Fin (lam.1.rowLen i), j.val := by
    have h := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈
        (Finset.univ : Finset (Fin (lam.1.colLen 0)))) => fin_injective_sum_lower (f i) (hf i))).mp hsum.symm
    exact (h i (Finset.mem_univ _)).symm
  let ix := lam.rowEquiv.symm x
  have h := fin_injective_minimal_sum (f ix.1) (hf ix.1) (hrow ix.1) ix.2
  change lam.colOf (g (lam.rowEquiv ix)) < _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h

lemma young_factorization {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    ∃ c : colSubgroup lam, ∃ a : rowSubgroup lam, g = c.1 * a.1 := by
  let r : Fin n → Fin n := fun x => lam.tableau
    ⟨(lam.rowOf x, lam.colOf (g x)), YoungDiagram.mem_iff_lt_rowLen.mpr (young_column_bound lam g htrans x)⟩
  have hr (x : Fin n) : lam.rowOf (r x) = lam.rowOf x := by simp [r, Partition.rowOf]
  have hc (x : Fin n) : lam.colOf (r x) = lam.colOf (g x) := by simp [r, Partition.colOf]
  have hi : Function.Injective r := by
    intro x y h
    apply htrans x y
    · simpa only [hr] using congrArg lam.rowOf h
    · simpa only [hc] using congrArg lam.colOf h
  let a : SymmetricGroup n := Equiv.ofBijective r ((Fintype.bijective_iff_injective_and_card r).mpr ⟨hi, rfl⟩)
  have ha : a ∈ rowSubgroup lam := hr
  have hca : g * a⁻¹ ∈ colSubgroup lam := by
    intro x
    have hh := hc (a⁻¹ x)
    change lam.colOf (a (a⁻¹ x)) = lam.colOf ((g * a⁻¹) x) at hh
    simpa using hh.symm
  refine ⟨⟨g * a⁻¹, hca⟩, ⟨a, ha⟩, ?_⟩
  simp

lemma young_collision {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (htrans : ¬ ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    ∃ a : rowSubgroup lam, ∃ c : colSubgroup lam,
      c.1 * g = g * a.1 ∧ complexSign n c.1 = -1 := by
  push Not at htrans
  obtain ⟨x, y, hr, hc, hxy⟩ := htrans
  refine ⟨⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩,
    ⟨Equiv.swap (g x) (g y), swap_mem_fiberSubgroup _ hc⟩, ?_, ?_⟩
  · apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  · simp [complexSign, Equiv.Perm.sign_swap (g.injective.ne hxy)]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Irreducibility
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

@[simp] lemma complexSign_inv {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g⁻¹ = complexSign n g := by
  simp [complexSign]

lemma polytabloid_left_column {n : ℕ} (lam : Partition n)
    (c : colSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (c.1 * g) = complexSign n c.1 * polytabloid lam g := by
  have h := congrArg (fun f : RegularSpace n => f g) (polytabloid_column_action lam c⁻¹)
  simpa only [regularRepresentation_apply, Subgroup.coe_inv, inv_inv, PiLp.smul_apply,
    smul_eq_mul, complexSign_inv] using h

lemma row_column_vector_eq {n : ℕ} (lam : Partition n) (f : RegularSpace n)
    (hr : ∀ (a : rowSubgroup lam) g, f (g * a.1) = f g)
    (hc : ∀ (c : colSubgroup lam) g, f (c.1 * g) = complexSign n c.1 * f g) :
    f = f 1 • polytabloid lam := by
  ext g
  change f g = f 1 * polytabloid lam g
  by_cases ht : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y
  · obtain ⟨c, a, rfl⟩ := young_factorization lam g ht
    rw [hr, polytabloid_right_row, ← mul_one c.1, hc, polytabloid_left_column,
      polytabloid_at_one]
    ring
  · obtain ⟨a, c, he, hs⟩ := young_collision lam g ht
    have hf : f g = 0 := by
      have h := hc c g
      rw [he, hr, hs, neg_one_mul] at h
      linear_combination h / 2
    have hp : polytabloid lam g = 0 := by
      have h := polytabloid_left_column lam c g
      rw [he, polytabloid_right_row, hs, neg_one_mul] at h
      linear_combination h / 2
    simp only [hf, hp, mul_zero]

lemma spechtGenerator_column_action {n : ℕ} (lam : Partition n) (c : colSubgroup lam) :
    spechtRepresentation lam c.1 (spechtGenerator lam) = complexSign n c.1 • spechtGenerator lam := by
  apply Subtype.ext
  exact polytabloid_column_action lam c

lemma specht_hom_ext {n : ℕ} (lam : Partition n)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E)
    (f g : Representation.IntertwiningMap (spechtRepresentation lam) ρ)
    (h : f (spechtGenerator lam) = g (spechtGenerator lam)) : f = g := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have haux : ∀ v (hv : v ∈ (spechtSubrepresentation lam).toSubmodule),
      f ⟨v, hv⟩ = g ⟨v, hv⟩ := by
    intro v hv
    change v ∈ Submodule.span ℂ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      change f (spechtRepresentation lam a (spechtGenerator lam)) =
        g (spechtRepresentation lam a (spechtGenerator lam))
      rw [f.isIntertwining, g.isIntertwining, h]
    | zero => exact (map_zero f).trans (map_zero g).symm
    | add x y hx hy hx' hy' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change y ∈ (spechtSubrepresentation lam).toSubmodule at hy
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      exact (map_add f (show Specht lam from ⟨x, hx⟩) (show Specht lam from ⟨y, hy⟩)).trans
        ((congrArg₂ (· + ·) hx' hy').trans (map_add g _ _).symm)
    | smul a x hx hx' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change f (a • (⟨x, hx⟩ : Specht lam)) = g (a • (⟨x, hx⟩ : Specht lam))
      exact (map_smul f a (show Specht lam from ⟨x, hx⟩)).trans
        ((congrArg (a • ·) hx').trans (map_smul g _ _).symm)
  exact haux (spechtInclusion lam x) x.property

lemma specht_endomorphism_scalar {n : ℕ} (lam : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation lam)) :
    ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap (spechtRepresentation lam)
      (spechtRepresentation lam)) := by
  let v := f (spechtGenerator lam)
  have hh : spechtInclusion lam v = (spechtInclusion lam v) 1 • polytabloid lam := by
    apply row_column_vector_eq
    · exact specht_right_row lam v
    · intro c g
      have he : spechtRepresentation lam (c⁻¹).1 v = complexSign n (c⁻¹).1 • v := by
        rw [← f.isIntertwining, spechtGenerator_column_action, map_smul]
      have h := congrArg (fun x => (spechtInclusion lam x) g) he
      change (spechtInclusion lam v) ((c⁻¹).1⁻¹ * g) =
        complexSign n (c⁻¹).1 * (spechtInclusion lam v) g at h
      simpa only [Subgroup.coe_inv, inv_inv, complexSign_inv] using h
  refine ⟨(spechtInclusion lam v) 1, specht_hom_ext lam (spechtRepresentation lam) _ _ ?_⟩
  apply Subtype.ext
  exact hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma invariant_starProjection_intertwines {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (S : Subrepresentation ρ) (g : G) (x : E) :
    S.toSubmodule.starProjection (ρ g x) = ρ g (S.toSubmodule.starProjection x) := by
  apply S.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact S.apply_mem_toSubmodule g (S.toSubmodule.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, representation_inner_inverse ρ hρ]
    exact S.toSubmodule.starProjection_inner_eq_zero x _ (S.apply_mem_toSubmodule g⁻¹ hw)

lemma irreducible_of_scalar_commutant {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (hscalar : ∀ f : Representation.IntertwiningMap ρ ρ,
      ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap ρ ρ)) :
    ρ.IsIrreducible := by
  have hb : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ E) hh
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hb⟩⟩
  refine ⟨?_⟩
  intro S
  let p : Representation.IntertwiningMap ρ ρ :=
    S.toSubmodule.starProjection.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ
      (invariant_starProjection_intertwines ρ hρ S)
  obtain ⟨z, hz⟩ := hscalar p
  have hp (x : E) : S.toSubmodule.starProjection x = z • x :=
    congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hz
  have hid (x : E) : (z * z) • x = z • x := by
    rw [mul_smul, ← hp, ← hp]
    exact S.toSubmodule.starProjection_eq_self_iff.mpr (S.toSubmodule.starProjection_apply_mem x)
  have hc : z * (z - 1) = 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have he : (z * (z - 1)) • x = 0 := by
      rw [mul_sub, mul_one, sub_smul, hid, sub_self]
    exact (smul_eq_zero.mp he).resolve_right hx
  rcases mul_eq_zero.mp hc with hz0 | hz1
  · left
    apply Subrepresentation.toSubmodule_injective
    apply eq_bot_iff.mpr
    intro x hx
    have he := S.toSubmodule.starProjection_eq_self_iff.mpr hx
    rw [hp, hz0, zero_smul] at he
    exact he.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply eq_top_iff.mpr
    intro x hx
    rw [sub_eq_zero] at hz1
    have he := S.toSubmodule.starProjection_apply_mem x
    rwa [hp, hz1, one_smul] at he

theorem specht_irreducible {n : ℕ} (lam : Partition n) :
    (spechtRepresentation lam).IsIrreducible :=
  irreducible_of_scalar_commutant _ (spechtRepresentation_norm lam)
    (specht_endomorphism_scalar lam)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MomentMonotonicity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma power_on_eigenvector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) {x : E} {c : ℂ} (hx : T x = c • x) (r : ℕ) :
    (T ^ r) x = c ^ r • x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

lemma trace_power_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (r : ℕ) :
    (LinearMap.trace ℂ E (T ^ r)).re =
      ∑ i : Fin (finrank ℂ E), hT.eigenvalues rfl i ^ r := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (hT.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [power_on_eigenvector T (hT.apply_eigenvectorBasis rfl i), inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal, OrthonormalBasis.norm_eq_one, Complex.ofReal_one, one_pow, mul_one,
    ← Complex.ofReal_pow, Complex.ofReal_re]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SpectralAngle
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma trace_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    (LinearMap.trace ℂ E T).re = ∑ i : Fin (Module.finrank ℂ E), hT.eigenvalues rfl i := by
  simpa only [pow_one] using trace_power_spectral T hT 1

lemma quadratic_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) :
    (inner ℂ x (T x)).re = ∑ i : Fin (Module.finrank ℂ E),
      hT.eigenvalues rfl i * ‖inner ℂ (hT.eigenvectorBasis rfl i) x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner x (T x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hT (hT.eigenvectorBasis rfl i) x, hT.apply_eigenvectorBasis,
    inner_smul_left, RCLike.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
  rw [show inner ℂ x (hT.eigenvectorBasis rfl i) *
      ((hT.eigenvalues rfl i : ℂ) * inner ℂ (hT.eigenvectorBasis rfl i) x) =
      (hT.eigenvalues rfl i : ℂ) * (inner ℂ (hT.eigenvectorBasis rfl i) x *
        inner ℂ x (hT.eigenvectorBasis rfl i)) by ring,
    ← inner_conj_symm x (hT.eigenvectorBasis rfl i), Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq]

lemma positive_commuting_projection (X P : E →ₗ[ℂ] E) (hX : X.IsPositive)
    (hP : P.IsSymmetric) (hPP : P * P = P) (hPX : P * X = X * P) :
    (P * X).IsPositive := by
  have he : P * X * P = P * X := by
    rw [mul_assoc, ← hPX, ← mul_assoc, hPP]
  have hp := hX.conj_adjoint P
  rw [hP.adjoint_eq] at hp
  change (P * X * P).IsPositive at hp
  exact he ▸ hp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

@[simp] lemma finiteRegularRepresentation_apply (g : G) (f : EuclideanSpace ℂ G) (h : G) :
    finiteRegularRepresentation g f h = f (g⁻¹ * h) := rfl

omit [FiniteDimensional ℂ E] in
@[simp] lemma coefficientAction_apply (ρ : Representation ℂ G E) (f : G → ℂ) (x : E) :
    coefficientAction ρ f x = ∑ g, f g • ρ g x := by
  simp [coefficientAction]

def conjugationSum (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  ∑ g, ρ g * T * ρ g⁻¹

omit [FiniteDimensional ℂ E] in
lemma conjugationSum_intertwines (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E)
    (h : G) (x : E) :
    conjugationSum ρ T (ρ h x) = ρ h (conjugationSum ρ T x) := by
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => (ρ g * T * ρ g⁻¹) (ρ h x))
  change (∑ g, (ρ (h * g) * T * ρ (h * g)⁻¹) (ρ h x)) = _ at he
  have hi : ρ h⁻¹ (ρ h x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [conjugationSum, LinearMap.sum_apply, ← he, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hi]

omit [FiniteDimensional ℂ E] in
lemma trace_conjugationSum (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E (conjugationSum ρ T) =
      (Fintype.card G : ℂ) * LinearMap.trace ℂ E T := by
  simp only [conjugationSum, map_sum]
  have h (g : G) : LinearMap.trace ℂ E (ρ g * T * ρ g⁻¹) = LinearMap.trace ℂ E T := by
    rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma conjugationSum_scalar (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (T : E →ₗ[ℂ] E) :
    conjugationSum ρ T =
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ) * LinearMap.trace ℂ E T) • 1 := by
  let A : Representation.IntertwiningMap ρ ρ :=
    (conjugationSum ρ T).intertwiningMap_of_isIntertwiningMap ρ ρ
      (conjugationSum_intertwines ρ T)
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective A
  have he : conjugationSum ρ T = z • (1 : E →ₗ[ℂ] E) := by
    ext x
    exact congrArg (fun a : Representation.IntertwiningMap ρ ρ => a x) hz.symm
  have hd : (finrank ℂ E : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℂ) (M := E)))
  have ht := congrArg (LinearMap.trace ℂ E) he
  rw [trace_conjugationSum, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  rw [he]
  congr 1
  field_simp
  linear_combination ht.symm

def matrixCoefficient (ρ : Representation ℂ G E) (v : E) : E →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun x := WithLp.toLp 2 (fun g => inner ℂ v (ρ g⁻¹ x))
  map_add' := by intro x y; ext g; simp
  map_smul' := by intro z x; ext g; simp

omit [Fintype G] [FiniteDimensional ℂ E] in
@[simp] lemma matrixCoefficient_apply (ρ : Representation ℂ G E) (v x : E) (g : G) :
    matrixCoefficient ρ v x g = inner ℂ v (ρ g⁻¹ x) := rfl

omit [FiniteDimensional ℂ E] in
lemma matrixCoefficient_intertwines (ρ : Representation ℂ G E) (v : E) (g : G) (x : E) :
    matrixCoefficient ρ v (ρ g x) = finiteRegularRepresentation g (matrixCoefficient ρ v x) := by
  ext h
  simp [← Module.End.mul_apply, ← map_mul]

omit [FiniteDimensional ℂ E] in
lemma matrixCoefficient_action (ρ : Representation ℂ G E) (v : E) (f : G → ℂ) (x : E) :
    matrixCoefficient ρ v (coefficientAction ρ f x) =
      coefficientAction finiteRegularRepresentation f (matrixCoefficient ρ v x) := by
  simp only [coefficientAction_apply, map_sum, map_smul, matrixCoefficient_intertwines]

lemma matrixCoefficient_inner (ρ : Representation ℂ G E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (v w x y : E) :
    inner ℂ (matrixCoefficient ρ v x) (matrixCoefficient ρ w y) =
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ)) * inner ℂ w v * inner ℂ x y := by
  calc
    _ = inner ℂ x (conjugationSum ρ (InnerProductSpace.rankOne ℂ v w).toLinearMap y) := by
      rw [PiLp.inner_apply, conjugationSum, LinearMap.sum_apply, inner_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [matrixCoefficient_apply, RCLike.inner_apply, Module.End.mul_apply,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
      rw [map_smul, inner_smul_right, inner_conj_symm]
      congr 1
      simpa only [inv_inv] using representation_inner_inverse ρ hρ g⁻¹ x v
    _ = _ := by
      rw [conjugationSum_scalar, InnerProductSpace.trace_rankOne,
        LinearMap.smul_apply, Module.End.one_apply, inner_smul_right]

def normalizedCoefficient (ρ : Representation ℂ G E) (v : E) : E →ₗ[ℂ] EuclideanSpace ℂ G :=
  (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) • matrixCoefficient ρ v

lemma normalizedCoefficient_inner (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (v w x y : E) :
    inner ℂ (normalizedCoefficient ρ v x) (normalizedCoefficient ρ w y) =
      inner ℂ w v * inner ℂ x y := by
  have hd : (0 : ℝ) < finrank ℂ E := by exact_mod_cast Module.finrank_pos (R := ℂ) (M := E)
  have hg : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hn : (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ))) ^ 2 *
      ((Fintype.card G : ℝ) / (finrank ℂ E : ℝ)) = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hn' : (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) ^ 2 *
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ)) = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_one]
      using congrArg (fun r : ℝ => (r : ℂ)) hn
  simp only [normalizedCoefficient, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal,
    matrixCoefficient_inner ρ hρ]
  calc
    _ = ((Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) ^ 2 *
        ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ))) * (inner ℂ w v * inner ℂ x y) := by ring
    _ = _ := by rw [hn', one_mul]

omit [FiniteDimensional ℂ E] in
lemma normalizedCoefficient_action (ρ : Representation ℂ G E) (v : E) (f : G → ℂ) (x : E) :
    normalizedCoefficient ρ v (coefficientAction ρ f x) =
      coefficientAction finiteRegularRepresentation f (normalizedCoefficient ρ v x) := by
  simp only [normalizedCoefficient, LinearMap.smul_apply, matrixCoefficient_action, map_smul]

lemma normalizedCoefficient_orthonormal (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) :
    Orthonormal ℂ (fun i : Fin (finrank ℂ E) × Fin (finrank ℂ E) =>
      normalizedCoefficient ρ (stdOrthonormalBasis ℂ E i.1) (stdOrthonormalBasis ℂ E i.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [normalizedCoefficient_inner ρ hρ]
  simp only [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal]
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [h₁, h₂, Eq.comm, Prod.ext_iff]

lemma positive_orthonormal_trace_le {I : Type*} [Fintype I] (T : E →ₗ[ℂ] E)
    (hT : T.IsPositive) (v : I → E) (hv : Orthonormal ℂ v) :
    ∑ i, (inner ℂ (v i) (T (v i))).re ≤ (LinearMap.trace ℂ E T).re := by
  simp_rw [quadratic_spectral T hT.isSymmetric]
  rw [Finset.sum_comm, trace_spectral T hT.isSymmetric]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.mul_sum]
  have hb := hv.sum_inner_products_le (s := Finset.univ) (hT.isSymmetric.eigenvectorBasis rfl j)
  simp only [OrthonormalBasis.norm_eq_one, one_pow] at hb
  simp only [norm_inner_symm (x := v _) (y := hT.isSymmetric.eigenvectorBasis rfl j)] at hb
  exact (mul_le_mul_of_nonneg_left hb (hT.nonneg_eigenvalues rfl j)).trans_eq (mul_one _)

lemma coefficientAction_positive (ρ : Representation ℂ G E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction ρ f).IsPositive := by
  let i : Fin (finrank ℂ E) := ⟨0, Module.finrank_pos⟩
  let v := stdOrthonormalBasis ℂ E i
  have hv : inner ℂ v v = 1 := by
    simpa only [v, ite_true] using
      orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal i i
  have hi (x y : E) :
      inner ℂ (normalizedCoefficient ρ v x) (normalizedCoefficient ρ v y) = inner ℂ x y := by
    rw [normalizedCoefficient_inner ρ hρ, hv, one_mul]
  refine ⟨?_, ?_⟩
  · intro x y
    rw [← hi, ← hi x, normalizedCoefficient_action, normalizedCoefficient_action]
    exact hf.isSymmetric _ _
  · intro x
    rw [← hi, normalizedCoefficient_action]
    exact hf.re_inner_nonneg_left _

lemma irreducible_trace_le_regular (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (finrank ℂ E : ℝ) * (LinearMap.trace ℂ E (coefficientAction ρ f)).re ≤
      (LinearMap.trace ℂ (EuclideanSpace ℂ G) (coefficientAction finiteRegularRepresentation f)).re := by
  have hb := positive_orthonormal_trace_le _ hf _ (normalizedCoefficient_orthonormal ρ hρ)
  have he (i : Fin (finrank ℂ E) × Fin (finrank ℂ E)) :
      (inner ℂ (normalizedCoefficient ρ (stdOrthonormalBasis ℂ E i.1) (stdOrthonormalBasis ℂ E i.2))
        (coefficientAction finiteRegularRepresentation f
          (normalizedCoefficient ρ (stdOrthonormalBasis ℂ E i.1) (stdOrthonormalBasis ℂ E i.2)))).re =
      (inner ℂ (stdOrthonormalBasis ℂ E i.2) (coefficientAction ρ f (stdOrthonormalBasis ℂ E i.2))).re := by
    rw [← normalizedCoefficient_action, normalizedCoefficient_inner ρ hρ]
    simp only [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal, ite_true, one_mul]
  simp only [he, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hb
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E), Complex.re_sum]
  exact hb

lemma finiteRegular_trace (f : G → ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ G) (coefficientAction finiteRegularRepresentation f) =
      (Fintype.card G : ℂ) * f 1 := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)]
  have h (i : G) : inner ℂ ((EuclideanSpace.basisFun G ℂ) i)
      (coefficientAction finiteRegularRepresentation f ((EuclideanSpace.basisFun G ℂ) i)) = f 1 := by
    simp [coefficientAction, PiLp.inner_apply, finiteRegularRepresentation_apply]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

def subgroupExtension (H : Subgroup G) :
    EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun f := WithLp.toLp 2 (fun g => if hg : g ∈ H then f ⟨g, hg⟩ else 0)
  map_add' := by intro x y; ext g; by_cases hg : g ∈ H <;> simp [hg]
  map_smul' := by intro z x; ext g; by_cases hg : g ∈ H <;> simp [hg]

omit [Fintype G] in
@[simp] lemma subgroupExtension_apply (H : Subgroup G) (f : EuclideanSpace ℂ H) (h : H) :
    subgroupExtension H f h = f h := by simp [subgroupExtension]

omit [Fintype G] in
@[simp] lemma subgroupExtension_apply_not_mem (H : Subgroup G) (f : EuclideanSpace ℂ H)
    (g : G) (hg : g ∉ H) : subgroupExtension H f g = 0 := by simp [subgroupExtension, hg]

lemma subgroup_sum_extension (H : Subgroup G) (f : H → ℂ) :
    ∑ g : G, (if hg : g ∈ H then f ⟨g, hg⟩ else 0) = ∑ h : H, f h := by
  classical
  symm
  apply Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective
  · intro g hg
    have hn : g ∉ H := by intro h; exact hg ⟨⟨g, h⟩, rfl⟩
    simp [hn]
  · intro h
    simp

lemma subgroupExtension_inner (H : Subgroup G) (x : EuclideanSpace ℂ H)
    (y : EuclideanSpace ℂ G) :
    inner ℂ (subgroupExtension H x) y = inner ℂ x (WithLp.toLp 2 (fun h : H => y h)) := by
  classical
  simp only [PiLp.inner_apply, subgroupExtension, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← subgroup_sum_extension]
  apply Finset.sum_congr rfl
  intro g _
  split <;> simp_all

lemma coefficientAction_subgroup (H : Subgroup G) (f : G → ℂ)
    (x : EuclideanSpace ℂ H) (i : H) :
    coefficientAction finiteRegularRepresentation f (subgroupExtension H x) i =
      coefficientAction finiteRegularRepresentation (fun h : H => f h) x i := by
  classical
  simp only [coefficientAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    finiteRegularRepresentation_apply, smul_eq_mul]
  rw [← subgroup_sum_extension]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g ∈ H
  · simp [hg, subgroupExtension, H.mul_mem (H.inv_mem hg) i.property]
    exact Or.inl rfl
  · have hgi : g⁻¹ * (i : G) ∉ H := by
      intro h
      apply hg
      have : g⁻¹ ∈ H := by simpa using H.mul_mem h (H.inv_mem i.property)
      simpa using H.inv_mem this
    simp [hg, subgroupExtension_apply_not_mem H x _ hgi]

lemma subgroup_coefficient_compression (H : Subgroup G) (f : G → ℂ)
    (x y : EuclideanSpace ℂ H) :
    inner ℂ (subgroupExtension H x)
      (coefficientAction finiteRegularRepresentation f (subgroupExtension H y)) =
    inner ℂ x (coefficientAction finiteRegularRepresentation (fun h : H => f h) y) := by
  rw [subgroupExtension_inner]
  congr 1
  ext i
  exact coefficientAction_subgroup H f y i

theorem subgroup_coefficient_positive (H : Subgroup G) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction finiteRegularRepresentation (fun h : H => f h)).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    rw [← inner_conj_symm, ← subgroup_coefficient_compression,
      ← hf.isSymmetric, ← inner_conj_symm, starRingEnd_self_apply]
    exact subgroup_coefficient_compression H f x y
  · intro x
    rw [inner_re_symm, ← subgroup_coefficient_compression H f x x]
    exact (Complex.nonneg_iff.mp (hf.inner_nonneg_right _)).1

theorem subgroup_irreducible_trace_bound (H : Subgroup G)
    (ρ : Representation ℂ H E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ h x, ‖ρ h x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ∧
    (finrank ℂ E : ℝ) *
        (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ≤
      ((Fintype.card H : ℝ) / (Fintype.card G : ℝ)) *
        (LinearMap.trace ℂ (EuclideanSpace ℂ G)
          (coefficientAction finiteRegularRepresentation f)).re := by
  have hpos := subgroup_coefficient_positive H f hf
  constructor
  · exact Complex.re_le_re (coefficientAction_positive ρ hρ _ hpos).trace_nonneg
  · have hb := irreducible_trace_le_regular ρ hρ _ hpos
    rw [finiteRegular_trace, Complex.mul_re] at hb
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
      OneMemClass.coe_one] at hb
    rw [finiteRegular_trace, Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    convert hb using 1
    field_simp

def bilateralRepresentation : Representation ℂ (G × G) (EuclideanSpace ℂ G) where
  toFun g := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.mulRight g.2⁻¹).trans (Equiv.mulLeft g.1))).toLinearEquiv.toLinearMap
  map_one' := by ext f h; change f (1⁻¹ * h * (1⁻¹)⁻¹) = f h; simp
  map_mul' := by
    intro g k; ext f h
    change f ((g.1 * k.1)⁻¹ * h * ((g.2 * k.2)⁻¹)⁻¹) =
      f (k.1⁻¹ * (g.1⁻¹ * h * (g.2⁻¹)⁻¹) * (k.2⁻¹)⁻¹)
    simp [mul_assoc]

@[simp] lemma bilateralRepresentation_apply (g : G × G) (f : EuclideanSpace ℂ G) (h : G) :
    bilateralRepresentation g f h = f (g.1⁻¹ * h * g.2) := by
  change f (g.1⁻¹ * h * (g.2⁻¹)⁻¹) = _
  rw [inv_inv]

lemma bilateralRepresentation_norm (g : G × G) (f : EuclideanSpace ℂ G) :
    ‖bilateralRepresentation g f‖ = ‖f‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.mulRight g.2⁻¹).trans (Equiv.mulLeft g.1))).norm_map f

@[simp] lemma bilateralRepresentation_left (g : G) :
    bilateralRepresentation (g, (1 : G)) = finiteRegularRepresentation g := by
  ext f h
  simp

lemma coefficientAction_right (f : G → ℂ) (g : G) (x : EuclideanSpace ℂ G) :
    coefficientAction finiteRegularRepresentation f (bilateralRepresentation (1, g) x) =
      bilateralRepresentation (1, g) (coefficientAction finiteRegularRepresentation f x) := by
  simp only [coefficientAction_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  ext i
  simp [mul_assoc]

def subgroupCoefficientCarrier (H : Subgroup G) (ρ : Representation ℂ H E) :
    Subrepresentation (bilateralRepresentation (G := G)) where
  toSubmodule := Submodule.span ℂ (Set.range (fun t : (G × G) × E × E =>
    bilateralRepresentation t.1 (subgroupExtension H (normalizedCoefficient ρ t.2.1 t.2.2))))
  apply_mem_toSubmodule g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨k, v, w⟩, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨(g * k, v, w), by simp only [map_mul, Module.End.mul_apply]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

def subgroupCoefficientProjection (H : Subgroup G) (ρ : Representation ℂ H E) :
    EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G :=
  (subgroupCoefficientCarrier H ρ).toSubmodule.starProjection.toLinearMap

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_intertwines (H : Subgroup G) (ρ : Representation ℂ H E)
    (g : G × G) (x : EuclideanSpace ℂ G) :
    subgroupCoefficientProjection H ρ (bilateralRepresentation g x) =
      bilateralRepresentation g (subgroupCoefficientProjection H ρ x) :=
  invariant_starProjection_intertwines _ bilateralRepresentation_norm (subgroupCoefficientCarrier H ρ) g x

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_commutes (H : Subgroup G) (ρ : Representation ℂ H E)
    (f : G → ℂ) :
    subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f =
      coefficientAction finiteRegularRepresentation f * subgroupCoefficientProjection H ρ := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, coefficientAction_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g _
  rw [← bilateralRepresentation_left]
  congr 1
  exact subgroupCoefficientProjection_intertwines H ρ (g, 1) x

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_symmetric (H : Subgroup G) (ρ : Representation ℂ H E) :
    (subgroupCoefficientProjection H ρ).IsSymmetric := by
  intro x y
  exact (subgroupCoefficientCarrier H ρ).toSubmodule.inner_starProjection_left_eq_right x y

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_idempotent (H : Subgroup G) (ρ : Representation ℂ H E) :
    subgroupCoefficientProjection H ρ * subgroupCoefficientProjection H ρ =
      subgroupCoefficientProjection H ρ := by
  apply LinearMap.ext
  intro x
  exact (subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_eq_self_iff.mpr
    ((subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_apply_mem x)

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_fixes (H : Subgroup G) (ρ : Representation ℂ H E) (v x : E) :
    subgroupCoefficientProjection H ρ (subgroupExtension H (normalizedCoefficient ρ v x)) =
      subgroupExtension H (normalizedCoefficient ρ v x) := by
  apply (subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_eq_self_iff.mpr
  apply Submodule.subset_span
  exact ⟨((1, 1), v, x), by simp only [show ((1, 1) : G × G) = 1 from rfl, map_one,
    Module.End.one_apply]⟩

lemma finiteRegular_coefficient_kernel (f : G → ℂ) (i j : G) :
    coefficientAction finiteRegularRepresentation f (EuclideanSpace.basisFun G ℂ j) i =
      f (i * j⁻¹) := by
  simp only [coefficientAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    finiteRegularRepresentation_apply, smul_eq_mul, EuclideanSpace.basisFun_apply]
  simp only [PiLp.single_apply, inv_mul_eq_iff_eq_mul, mul_ite, mul_one, mul_zero]
  have he (x : G) : i = x * j ↔ x = i * j⁻¹ := by
    constructor
    · intro h; rw [h, mul_inv_cancel_right]
    · intro h; rw [h, inv_mul_cancel_right]
  simp_rw [he]
  simp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges2
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma coefficientAction_eq_of_right_intertwines
    (T : EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G)
    (hT : ∀ g x, T (bilateralRepresentation (1, g) x) = bilateralRepresentation (1, g) (T x)) :
    coefficientAction finiteRegularRepresentation
      (fun g => T (EuclideanSpace.basisFun G ℂ 1) g) = T := by
  apply (EuclideanSpace.basisFun G ℂ).toBasis.ext
  intro j
  have he : bilateralRepresentation (1, j⁻¹) (EuclideanSpace.basisFun G ℂ 1) =
      EuclideanSpace.basisFun G ℂ j := by
    ext i
    simp [EuclideanSpace.basisFun_apply, mul_inv_eq_one]
  change coefficientAction finiteRegularRepresentation
    (fun g => T (EuclideanSpace.basisFun G ℂ 1) g) (EuclideanSpace.basisFun G ℂ j) =
      T (EuclideanSpace.basisFun G ℂ j)
  rw [← he, hT]
  ext i
  rw [he, finiteRegular_coefficient_kernel, bilateralRepresentation_apply]
  simp

def supportedCoefficients (H : Subgroup G) (ρ : Representation ℂ H E) (f : G → ℂ) : G → ℂ :=
  fun g => (subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f)
    (EuclideanSpace.basisFun G ℂ 1) g

omit [FiniteDimensional ℂ E] in
lemma supportedCoefficients_action (H : Subgroup G) (ρ : Representation ℂ H E) (f : G → ℂ) :
    coefficientAction finiteRegularRepresentation (supportedCoefficients H ρ f) =
      subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f := by
  apply coefficientAction_eq_of_right_intertwines
  intro g x
  simp only [Module.End.mul_apply, coefficientAction_right, subgroupCoefficientProjection_intertwines]

omit [FiniteDimensional ℂ E] in
lemma supportedCoefficients_positive (H : Subgroup G) (ρ : Representation ℂ H E) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction finiteRegularRepresentation (supportedCoefficients H ρ f)).IsPositive := by
  rw [supportedCoefficients_action]
  exact positive_commuting_projection _ _ hf (subgroupCoefficientProjection_symmetric H ρ)
    (subgroupCoefficientProjection_idempotent H ρ) (subgroupCoefficientProjection_commutes H ρ f)

lemma supportedCoefficients_subgroup_action (H : Subgroup G) (ρ : Representation ℂ H E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ h x, ‖ρ h x‖ = ‖x‖) (f : G → ℂ) :
    coefficientAction ρ (fun h : H => supportedCoefficients H ρ f h) =
      coefficientAction ρ (fun h : H => f h) := by
  let i : Fin (finrank ℂ E) := ⟨0, Module.finrank_pos⟩
  let v := stdOrthonormalBasis ℂ E i
  have hv : inner ℂ v v = 1 := by
    simpa only [v, ite_true] using
      orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal i i
  have hc (a : G → ℂ) (x y : E) :
      inner ℂ x (coefficientAction ρ (fun h : H => a h) y) =
      inner ℂ (subgroupExtension H (normalizedCoefficient ρ v x))
        (coefficientAction finiteRegularRepresentation a
          (subgroupExtension H (normalizedCoefficient ρ v y))) := by
    rw [subgroup_coefficient_compression, ← normalizedCoefficient_action,
      normalizedCoefficient_inner ρ hρ, hv, one_mul]
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [hc, hc, supportedCoefficients_action, Module.End.mul_apply,
    ← subgroupCoefficientProjection_symmetric H ρ, subgroupCoefficientProjection_fixes]

theorem subgroup_supported_trace_bound (H : Subgroup G) (ρ : Representation ℂ H E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ h x, ‖ρ h x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ∧
    (finrank ℂ E : ℝ) *
        (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ≤
      ((Fintype.card H : ℝ) / (Fintype.card G : ℝ)) *
        (LinearMap.trace ℂ (EuclideanSpace ℂ G)
          (subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f)).re := by
  have hb := subgroup_irreducible_trace_bound H ρ hρ (supportedCoefficients H ρ f)
    (supportedCoefficients_positive H ρ f hf)
  rw [supportedCoefficients_subgroup_action H ρ hρ, supportedCoefficients_action] at hb
  exact hb

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {G : Type*} [Fintype G] [Group G]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
variable (c : A → I) (d : A → J) (i₀ : I)
variable (hinj : Function.Injective (fun x => (c x,d x)))
variable (hfull : ∀ j, ∃ x, c x = i₀ ∧ d x = j)

include hinj hfull

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.IrreducibleClassification
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

def columnStatistic {n : ℕ} (lam : Partition n) : ℕ :=
  ∑ x : Fin n, lam.colOf x

lemma row_column_transversal_statistic {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y) :
    columnStatistic mu ≤ columnStatistic lam := by
  unfold columnStatistic
  rw [← Equiv.sum_comp g lam.colOf,
    ← Equiv.sum_comp mu.rowEquiv (fun y => lam.colOf (g y)),
    ← Equiv.sum_comp mu.rowEquiv mu.colOf, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [Partition.colOf_rowEquiv]
  apply Finset.sum_le_sum
  intro i _
  apply fin_injective_sum_lower
  intro j k h
  have he := ht (mu.rowEquiv ⟨i, j⟩) (mu.rowEquiv ⟨i, k⟩) (by simp) h
  exact Sigma.mk.inj_iff.mp (mu.rowEquiv.injective he) |>.2 |> eq_of_heq

lemma row_column_transversal_bound_of_statistic_eq {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (hstat : columnStatistic lam = columnStatistic mu) (x : Fin n) :
    lam.colOf (g x) < mu.1.rowLen (mu.rowOf x) := by
  let f := fun i : Fin (mu.1.colLen 0) => fun j : Fin (mu.1.rowLen i) =>
    lam.colOf (g (mu.rowEquiv ⟨i, j⟩))
  have hf (i : Fin (mu.1.colLen 0)) : Function.Injective (f i) := by
    intro j k h
    have he := ht (mu.rowEquiv ⟨i, j⟩) (mu.rowEquiv ⟨i, k⟩) (by simp) h
    exact Sigma.mk.inj_iff.mp (mu.rowEquiv.injective he) |>.2 |> eq_of_heq
  have hsum : ∑ i, ∑ j, f i j = ∑ i : Fin (mu.1.colLen 0), ∑ j : Fin (mu.1.rowLen i), j.val := by
    unfold columnStatistic at hstat
    rw [← Equiv.sum_comp g lam.colOf,
      ← Equiv.sum_comp mu.rowEquiv (fun y => lam.colOf (g y)),
      ← Equiv.sum_comp mu.rowEquiv mu.colOf, Fintype.sum_sigma, Fintype.sum_sigma] at hstat
    simpa only [Partition.colOf_rowEquiv] using hstat
  have hrow (i : Fin (mu.1.colLen 0)) : ∑ j, f i j = ∑ j : Fin (mu.1.rowLen i), j.val := by
    have h := Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin (mu.1.colLen 0)))) =>
      fin_injective_sum_lower (f i) (hf i))
    exact (h.mp hsum.symm i (Finset.mem_univ _)).symm
  let ix := mu.rowEquiv.symm x
  have hh := fin_injective_minimal_sum (f ix.1) (hf ix.1) (hrow ix.1) ix.2
  change lam.colOf (g (mu.rowEquiv ix)) < _ at hh
  rw [Equiv.apply_symm_apply] at hh
  exact hh

def columnPositionsEquiv {n : ℕ} (lam : Partition n) (j : ℕ) :
    Fin (lam.1.colLen j) ≃ {x : Fin n // lam.colOf x = j} where
  toFun i := ⟨lam.tableau ⟨(i.val, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩,
    by simp [Partition.colOf]⟩
  invFun x := ⟨lam.rowOf x.1, by
    have h := YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x.1).property
    change lam.rowOf x.1 < lam.1.colLen (lam.colOf x.1) at h
    simpa only [x.2] using h⟩
  left_inv i := by ext; simp [Partition.rowOf]
  right_inv x := by
    apply Subtype.ext
    apply lam.tableau.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    exact Prod.ext rfl x.2.symm

lemma colOf_fiber_card {n : ℕ} (lam : Partition n) (j : ℕ) :
    Fintype.card {x : Fin n // lam.colOf x = j} = lam.1.colLen j := by
  simpa using (Fintype.card_congr (columnPositionsEquiv lam j)).symm

lemma row_column_transversal_eq_of_statistic_eq {n : ℕ} (lam mu : Partition n)
    (g : SymmetricGroup n)
    (ht : ∀ x y, mu.rowOf x = mu.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y)
    (hstat : columnStatistic lam = columnStatistic mu) : lam = mu := by
  let r : Fin n → Fin n := fun x => mu.tableau
    ⟨(mu.rowOf x, lam.colOf (g x)), YoungDiagram.mem_iff_lt_rowLen.mpr
      (row_column_transversal_bound_of_statistic_eq lam mu g ht hstat x)⟩
  have hr (x : Fin n) : mu.rowOf (r x) = mu.rowOf x := by simp [r, Partition.rowOf]
  have hc (x : Fin n) : mu.colOf (r x) = lam.colOf (g x) := by simp [r, Partition.colOf]
  have hi : Function.Injective r := by
    intro x y h
    apply ht x y
    · simpa only [hr] using congrArg mu.rowOf h
    · simpa only [hc] using congrArg mu.colOf h
  let a : SymmetricGroup n := Equiv.ofBijective r (⟨hi, Finite.surjective_of_injective hi⟩)
  let e : SymmetricGroup n := g.symm.trans a
  have he (x : Fin n) : mu.colOf (e x) = lam.colOf x := by
    change mu.colOf (r (g⁻¹ x)) = lam.colOf x
    rw [hc]
    exact congrArg lam.colOf (g.apply_symm_apply x)
  have hcol (j : ℕ) : lam.1.colLen j = mu.1.colLen j := by
    rw [← colOf_fiber_card lam j, ← colOf_fiber_card mu j]
    exact Fintype.card_congr (Equiv.subtypeEquiv e (by intro x; rw [he]))
  apply Subtype.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen, hcol]

lemma specht_hom_generator_ne_zero {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) : f (spechtGenerator lam) ≠ 0 := by
  intro h
  apply hf
  apply specht_hom_ext lam _
  simpa using h

lemma specht_hom_transversal {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) :
    ∃ g : SymmetricGroup n, ∀ x y, mu.rowOf x = mu.rowOf y →
      lam.colOf (g x) = lam.colOf (g y) → x = y := by
  let v : RegularSpace n := spechtInclusion mu (f (spechtGenerator lam))
  have hv : v ≠ 0 := by
    intro h
    apply specht_hom_generator_ne_zero lam mu f hf
    exact Subtype.ext h
  obtain ⟨g, hg⟩ : ∃ g, v g ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    ext g
    exact h g
  have hvcol (c : colSubgroup lam) (g : SymmetricGroup n) :
      v (c.1 * g) = complexSign n c.1 * v g := by
    have he := Representation.IntertwiningMap.isIntertwining _ _ f (c⁻¹).1 (spechtGenerator lam)
    rw [spechtGenerator_column_action, map_smul] at he
    have hh := congrArg (fun w => (spechtInclusion mu w) g) he
    change complexSign n (c⁻¹).1 * v g = v ((c⁻¹).1⁻¹ * g) at hh
    simpa only [Subgroup.coe_inv, inv_inv, complexSign_inv] using hh.symm
  refine ⟨g, ?_⟩
  intro x y hr hc
  by_contra hxy
  let a : rowSubgroup mu := ⟨Equiv.swap x y, swap_mem_fiberSubgroup _ hr⟩
  let c : colSubgroup lam := ⟨Equiv.swap (g x) (g y), swap_mem_fiberSubgroup _ hc⟩
  have he : c.1 * g = g * a.1 := by
    apply Equiv.ext
    intro z
    exact g.injective.swap_apply x y z
  have hs : complexSign n c.1 = -1 := by
    simp [c, complexSign, Equiv.Perm.sign_swap (g.injective.ne hxy)]
  have hh := hvcol c g
  rw [he, specht_right_row mu (f (spechtGenerator lam)), hs, neg_one_mul] at hh
  apply hg
  linear_combination hh / 2

lemma specht_hom_columnStatistic {n : ℕ} (lam mu : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation mu))
    (hf : f ≠ 0) : columnStatistic mu ≤ columnStatistic lam := by
  obtain ⟨g, hg⟩ := specht_hom_transversal lam mu f hf
  exact row_column_transversal_statistic lam mu g hg

lemma specht_equiv_shape_eq {n : ℕ} (lam mu : Partition n)
    (f : Representation.Equiv (spechtRepresentation lam) (spechtRepresentation mu)) :
    lam = mu := by
  have hf : f.toIntertwiningMap ≠ 0 := by
    intro h
    have hh := congrArg (fun k : Representation.IntertwiningMap
      (spechtRepresentation lam) (spechtRepresentation mu) => k (spechtGenerator lam)) h
    apply spechtGenerator_ne_zero lam
    exact f.toLinearEquiv.injective (by simpa using hh)
  have hi : f.symm.toIntertwiningMap ≠ 0 := by
    intro h
    have hh := congrArg (fun k : Representation.IntertwiningMap
      (spechtRepresentation mu) (spechtRepresentation lam) => k (spechtGenerator mu)) h
    apply spechtGenerator_ne_zero mu
    exact f.symm.toLinearEquiv.injective (by simpa using hh)
  have hs := le_antisymm (specht_hom_columnStatistic _ _ f.symm.toIntertwiningMap hi)
    (specht_hom_columnStatistic _ _ f.toIntertwiningMap hf)
  obtain ⟨g, hg⟩ := specht_hom_transversal lam mu f.toIntertwiningMap hf
  exact row_column_transversal_eq_of_statistic_eq lam mu g hg hs

def natPartitionOfDiagram {n : ℕ} (lam : Partition n) : Nat.Partition n where
  parts := lam.1.rowLens
  parts_pos := by
    intro i hi
    exact lam.1.pos_of_mem_rowLens i hi
  parts_sum := partition_rowLens_sum lam

def diagramOfNatPartition {n : ℕ} (p : Nat.Partition n) : Partition n :=
  ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
      (p.parts.pairwise_sort (· ≥ ·)).sortedGE, by
    rw [← diagram_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self]
    · simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum
    · intro a ha
      exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp ha)⟩

@[simp]
lemma natPartitionOfDiagram_diagramOfNatPartition {n : ℕ} (p : Nat.Partition n) :
    natPartitionOfDiagram (diagramOfNatPartition p) = p := by
  apply Nat.Partition.ext
  dsimp [natPartitionOfDiagram, diagramOfNatPartition]
  rw [YoungDiagram.rowLens_ofRowLens_eq_self]
  · exact Multiset.sort_eq _ _
  · intro a ha
    exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp ha)

@[simp]
lemma diagramOfNatPartition_natPartitionOfDiagram {n : ℕ} (lam : Partition n) :
    diagramOfNatPartition (natPartitionOfDiagram lam) = lam := by
  apply Subtype.ext
  change YoungDiagram.ofRowLens ((↑lam.1.rowLens : Multiset ℕ).sort (· ≥ ·))
    ((↑lam.1.rowLens : Multiset ℕ).pairwise_sort (· ≥ ·)).sortedGE = lam.1
  have hs : (↑lam.1.rowLens : Multiset ℕ).sort (· ≥ ·) = lam.1.rowLens := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ lam.1.rowLens_sorted.pairwise
  simpa only [hs] using (YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := lam.1))

def conjugacyDiagram (n : ℕ) : ConjClasses (SymmetricGroup n) → Partition n :=
  Quotient.lift (fun g : SymmetricGroup n =>
    diagramOfNatPartition (show Nat.Partition n from Fintype.card_fin n ▸ g.partition)) (by
      intro g h hgh
      have he := Equiv.Perm.partition_eq_of_isConj.mp hgh
      apply congrArg diagramOfNatPartition
      exact congrArg (fun p : Nat.Partition (Fintype.card (Fin n)) =>
        show Nat.Partition n from Fintype.card_fin n ▸ p) he)

lemma conjugacyDiagram_injective (n : ℕ) : Function.Injective (conjugacyDiagram n) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
      intro he
      apply Quotient.sound
      apply Equiv.Perm.partition_eq_of_isConj.mpr
      have hh := congrArg natPartitionOfDiagram he
      simp only [conjugacyDiagram, Quotient.lift_mk,
        natPartitionOfDiagram_diagramOfNatPartition] at hh
      simpa using hh

def quotientCharacter {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (ρ : Representation ℂ G E) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (by
    intro g h hgh
    obtain ⟨k, rfl⟩ := isConj_iff.mp hgh
    exact (ρ.char_conj g k).symm)

@[simp]
lemma quotientCharacter_mk {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (ρ : Representation ℂ G E) (g : G) :
    quotientCharacter ρ (ConjClasses.mk g) = ρ.character g := rfl

def classCharacterPairing {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) : (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g : G, f (ConjClasses.mk g) * ρ.character g⁻¹
  map_add' f g := by simp [Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' c f := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

lemma specht_classCharacterPairing {n : ℕ} (lam mu : Partition n) :
    classCharacterPairing (spechtRepresentation lam)
      (quotientCharacter (spechtRepresentation mu)) = if lam = mu then 1 else 0 := by
  let := specht_irreducible lam
  let := specht_irreducible mu
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  change (Nat.card (SymmetricGroup n) : ℂ)⁻¹ * ∑ g,
    (spechtRepresentation mu).character g * (spechtRepresentation lam).character g⁻¹ = _
  rw [Representation.char_orthonormal]
  congr 1
  apply propext
  constructor
  · rintro ⟨e⟩
    exact specht_equiv_shape_eq lam mu e
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

lemma specht_characters_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (fun lam : Partition n => quotientCharacter (spechtRepresentation lam)) := by
  rw [linearIndependent_iff']
  intro s c hc lam hlam
  have h := congrArg (classCharacterPairing (spechtRepresentation lam)) hc
  simpa only [map_sum, map_smul, map_zero, specht_classCharacterPairing,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hlam] using h

lemma specht_characters_span (n : ℕ) :
    Submodule.span ℂ (Set.range (fun lam : Partition n =>
      quotientCharacter (spechtRepresentation lam))) = ⊤ := by
  let := Fintype.ofFinite (Partition n)
  let := Fintype.ofFinite (ConjClasses (SymmetricGroup n))
  let : Nonempty (Partition n) := ⟨conjugacyDiagram n 1⟩
  have hle : Module.finrank ℂ (ConjClasses (SymmetricGroup n) → ℂ) ≤
      Fintype.card (Partition n) := by
    rw [Module.finrank_pi]
    exact Fintype.card_le_of_injective _ (conjugacyDiagram_injective n)
  exact (specht_characters_linearIndependent n).span_eq_top_of_card_eq_finrank
    (le_antisymm (specht_characters_linearIndependent n).fintype_card_le_finrank hle)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TraceDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

lemma class_function_expansion {n : ℕ} (f : ConjClasses (SymmetricGroup n) → ℂ) :
    f = ∑ lam : Partition n, classCharacterPairing (spechtRepresentation lam) f •
      quotientCharacter (spechtRepresentation lam) := by
  have hf : f ∈ Submodule.span ℂ (Set.range (fun lam : Partition n =>
    quotientCharacter (spechtRepresentation lam))) := by rw [specht_characters_span]; trivial
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨mu, rfl⟩ := hx
    simp only [specht_classCharacterPairing, ite_smul, one_smul, zero_smul]
    simp
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul c x _ hx =>
    simp only [map_smul, smul_assoc, ← Finset.smul_sum]
    rw [← hx]

theorem character_specht_expansion {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (g : SymmetricGroup n) :
    ρ.character g = ∑ lam : Partition n,
      (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
        (spechtRepresentation lam).character g := by
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  have he := congrFun (class_function_expansion (quotientCharacter ρ)) (ConjClasses.mk g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, quotientCharacter_mk] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro lam _
  congr 1
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank _ _

lemma trace_coefficientAction {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (f : G → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f) = ∑ g, f g * ρ.character g := by
  simp only [coefficientAction, map_sum, map_smul, smul_eq_mul, Representation.character]

theorem trace_specht_expansion {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (f : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f) =
      ∑ lam : Partition n,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
          LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f) := by
  simp only [trace_coefficientAction, character_specht_expansion ρ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lam _
  apply Finset.sum_congr rfl
  intro g _
  ring

lemma finiteRegular_character {G : Type*} [Group G] [Fintype G] (g : G) :
    (finiteRegularRepresentation (G := G)).character g =
      if g = 1 then (Fintype.card G : ℂ) else 0 := by
  have he : coefficientAction (finiteRegularRepresentation (G := G))
      (fun h => if h = g then 1 else 0) = finiteRegularRepresentation g := by
    simp [coefficientAction, ite_smul]
  rw [Representation.character, ← he, finiteRegular_trace]
  by_cases hg : g = 1
  · simp [hg]
  · simp [hg, Ne.symm hg]

lemma specht_regular_multiplicity {n : ℕ} (lam : Partition n) :
    finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam)
      (finiteRegularRepresentation (G := SymmetricGroup n))) = spechtDimension lam := by
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  apply Nat.cast_injective (R := ℂ)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [finiteRegular_character, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, inv_one, Representation.char_one, Fintype.card_eq_nat_card]
  have hg : (Nat.card (SymmetricGroup n) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]
  rfl

theorem regular_trace_specht_expansion {n : ℕ} (f : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (SymmetricGroup n))
      (coefficientAction finiteRegularRepresentation f) =
      ∑ lam : Partition n, (spechtDimension lam : ℂ) *
        LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f) := by
  rw [trace_specht_expansion]
  simp only [specht_regular_multiplicity]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.RestrictionSum
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
variable {G E F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

def mixedConjugationSum (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F := ∑ g, (σ g).comp (T.comp (ρ g⁻¹))

lemma mixedConjugationSum_intertwines {G E F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E)
    (σ : Representation ℂ G F) (T : E →ₗ[ℂ] F) (h : G) (x : E) :
    mixedConjugationSum ρ σ T (ρ h x) = σ h (mixedConjugationSum ρ σ T x) := by
  have he := Equiv.sum_comp (Equiv.mulLeft h)
    (fun g : G => σ g (T (ρ g⁻¹ (ρ h x))))
  change (∑ g, σ (h * g) (T (ρ (h * g)⁻¹ (ρ h x)))) = _ at he
  have hi : ρ h⁻¹ (ρ h x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hi]

lemma matrixCoefficient_inner_eq_zero (ρ : Representation ℂ G E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ σ, f = 0) (v x : E) (w y : F) :
    inner ℂ (matrixCoefficient σ w y) (matrixCoefficient ρ v x) = 0 := by
  let T : E →ₗ[ℂ] F := (InnerProductSpace.rankOne ℂ w v).toLinearMap
  let A : Representation.IntertwiningMap ρ σ :=
    (mixedConjugationSum ρ σ T).intertwiningMap_of_isIntertwiningMap ρ σ
      (mixedConjugationSum_intertwines ρ σ T)
  have hz : mixedConjugationSum ρ σ T x = 0 :=
    congrArg (fun f : Representation.IntertwiningMap ρ σ => f x) (hn A)
  calc
    _ = inner ℂ y (mixedConjugationSum ρ σ T x) := by
      rw [PiLp.inner_apply, mixedConjugationSum, LinearMap.sum_apply, inner_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [matrixCoefficient_apply, RCLike.inner_apply, LinearMap.comp_apply,
        T, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
      rw [map_smul, inner_smul_right, inner_conj_symm]
      congr 1
      simpa only [inv_inv] using representation_inner_inverse σ hσ g⁻¹ y w
    _ = 0 := by rw [hz, inner_zero_right]

lemma bilateral_matrixCoefficient {G F : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (σ : Representation ℂ G F)
    (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (a b : G) (w y : F) :
    bilateralRepresentation (a, b) (matrixCoefficient σ w y) =
      matrixCoefficient σ (σ b w) (σ a y) := by
  ext g
  rw [bilateralRepresentation_apply, matrixCoefficient_apply, matrixCoefficient_apply,
    representation_inner_inverse σ hσ]
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, inv_inv]

lemma subgroup_coefficient_orthogonal (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ (σ.comp H.subtype), f = 0)
    (v x : E) (w y : F) :
    inner ℂ (subgroupExtension H (normalizedCoefficient ρ v x))
      (matrixCoefficient σ w y) = 0 := by
  rw [subgroupExtension_inner]
  change inner ℂ (normalizedCoefficient ρ v x) (matrixCoefficient (σ.comp H.subtype) w y) = 0
  rw [normalizedCoefficient, LinearMap.smul_apply, inner_smul_left]
  have he := matrixCoefficient_inner_eq_zero ρ (σ.comp H.subtype)
    (fun h => hσ h) hn v x w y
  have hh : inner ℂ (matrixCoefficient ρ v x) (matrixCoefficient (σ.comp H.subtype) w y) = 0 := by
    rw [← inner_conj_symm, he, map_zero]
  rw [hh, mul_zero]

lemma subgroupCoefficientProjection_kills (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ (σ.comp H.subtype), f = 0)
    (w y : F) :
    subgroupCoefficientProjection H ρ (matrixCoefficient σ w y) = 0 := by
  apply ((subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_apply_eq_zero_iff).mpr
  rw [Submodule.mem_orthogonal]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨⟨a, b⟩, v, x⟩, rfl⟩ := hz
    change inner ℂ (bilateralRepresentation (a, b)
      (subgroupExtension H (normalizedCoefficient ρ v x))) (matrixCoefficient σ w y) = 0
    rw [representation_inner_inverse (bilateralRepresentation (G := G))
      (bilateralRepresentation_norm (G := G)) (a,b),
      show (a,b)⁻¹ = (a⁻¹,b⁻¹) by rfl, bilateral_matrixCoefficient σ hσ]
    exact subgroup_coefficient_orthogonal H ρ σ hσ hn v x _ _
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul c x _ hx => simp [inner_smul_left, hx]

lemma supportedCoefficients_kills (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hn : ∀ f : Representation.IntertwiningMap ρ (σ.comp H.subtype), f = 0)
    (f : G → ℂ) : coefficientAction σ (supportedCoefficients H ρ f) = 0 := by
  ext y
  apply ext_inner_left ℂ
  intro w
  have he := matrixCoefficient_action σ w (supportedCoefficients H ρ f) y
  rw [supportedCoefficients_action, subgroupCoefficientProjection_commutes,
    Module.End.mul_apply, subgroupCoefficientProjection_kills H ρ σ hσ hn w y, map_zero] at he
  have ht := congrArg (fun v : EuclideanSpace ℂ G => v 1) he
  simpa only [matrixCoefficient_apply, inv_one, map_one, Module.End.one_apply,
    PiLp.zero_apply, LinearMap.zero_apply, inner_zero_right] using ht

lemma coefficientAction_sub {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (f h : G → ℂ) :
    coefficientAction ρ (f - h) = coefficientAction ρ f - coefficientAction ρ h := by
  simp only [coefficientAction, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma supportedCoefficients_difference_positive {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : Subgroup G) (ρ : Representation ℂ H E)
    (f : G → ℂ) (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction finiteRegularRepresentation (f - supportedCoefficients H ρ f)).IsPositive := by
  let P := subgroupCoefficientProjection H ρ
  let X := coefficientAction finiteRegularRepresentation f
  have hP : P.IsSymmetric := subgroupCoefficientProjection_symmetric H ρ
  have hPP : P * P = P := subgroupCoefficientProjection_idempotent H ρ
  have hPX : P * X = X * P := subgroupCoefficientProjection_commutes H ρ f
  have hPXp : P * X * P = P * X := by
    rw [mul_assoc, ← hPX, ← mul_assoc, hPP]
  have he : (1 - P) * X * (1 - P) = X - P * X := by
    simp only [sub_mul, one_mul, mul_sub, mul_one, ← hPX, hPXp, sub_self, sub_zero]
  have hp := hf.conj_adjoint (1 - P)
  rw [(LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one hP).adjoint_eq] at hp
  change ((1 - P) * X * (1 - P)).IsPositive at hp
  rw [he] at hp
  rw [coefficientAction_sub, supportedCoefficients_action]
  exact hp

lemma supportedCoefficients_trace_le (H : Subgroup G) (ρ : Representation ℂ H E)
    (σ : Representation ℂ G F) [σ.IsIrreducible] [Nontrivial F]
    (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (LinearMap.trace ℂ F (coefficientAction σ (supportedCoefficients H ρ f))).re ≤
      (LinearMap.trace ℂ F (coefficientAction σ f)).re := by
  have hp := coefficientAction_positive σ hσ _ (supportedCoefficients_difference_positive H ρ f hf)
  rw [coefficientAction_sub] at hp
  have ht := Complex.re_le_re hp.trace_nonneg
  simpa only [map_sub, Complex.sub_re, Complex.zero_re, sub_nonneg] using ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

def RestrictionEligible {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H : Subgroup (SymmetricGroup n)) (ρ : Representation ℂ H E) (lam : Partition n) : Prop :=
  ∃ f : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp H.subtype), f ≠ 0

theorem specht_positive_restriction {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : Subgroup (SymmetricGroup n)) (ρ : Representation ℂ H E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ∧
    (finrank ℂ E : ℝ) * (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ≤
      ((Fintype.card H : ℝ) / (Fintype.card (SymmetricGroup n) : ℝ)) *
        ∑ lam : Partition n, if RestrictionEligible H ρ lam then
          (spechtDimension lam : ℝ) *
            (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re
        else 0 := by
  have hb := subgroup_supported_trace_bound H ρ hρ f hf
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← supportedCoefficients_action, regular_trace_specht_expansion, Complex.re_sum]
  apply Finset.sum_le_sum
  intro lam _
  let := specht_irreducible lam
  by_cases he : RestrictionEligible H ρ lam
  · simp only [if_pos he, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left
      (supportedCoefficients_trace_le H ρ (spechtRepresentation lam) (spechtRepresentation_norm lam) f hf)
      (Nat.cast_nonneg _)
  · have hn : ∀ f : Representation.IntertwiningMap ρ
        ((spechtRepresentation lam).comp H.subtype), f = 0 := by
      intro f
      by_contra hn
      exact he ⟨f, hn⟩
    rw [supportedCoefficients_kills H ρ (spechtRepresentation lam)
      (spechtRepresentation_norm lam) hn f]
    simp [he]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical
variable {G H E F L : Type*} [Monoid G] [Monoid H]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup L] [Module ℂ L]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical
open scoped BigOperators TensorProduct Classical

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.InjectionRestriction
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma irreducible_comp_surjective {G H E : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [Nontrivial E]
    (ρ : Representation ℂ G E) [ρ.IsIrreducible] (j : H →* G)
    (hj : Function.Surjective j) : Representation.IsIrreducible (ρ.comp j) := by
  have hb : (⊥ : Subrepresentation (ρ.comp j)) ≠ ⊤ := by
    intro he
    exact bot_ne_top (α := Submodule ℂ E) (congrArg Subrepresentation.toSubmodule he)
  let : Nontrivial (Subrepresentation (ρ.comp j)) := ⟨⟨⊥,⊤,hb⟩⟩
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule g x hx := by
      obtain ⟨h,rfl⟩ := hj g
      exact S.apply_mem_toSubmodule h hx }
  rcases eq_bot_or_eq_top T with ht | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_comp_equiv {H : Type*} [Group H] [Fintype H]
    (ρ : Representation ℂ G E) (e : G ≃* H) (f : H → ℂ) :
    coefficientAction (ρ.comp e.symm.toMonoidHom) f =
      coefficientAction ρ (fun g => f (e g)) := by
  unfold coefficientAction
  rw [← Equiv.sum_comp e.toEquiv]
  simp

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma restrictionEligible_range_iff {n : ℕ} (ρ : Representation ℂ G E)
    (i : G →* SymmetricGroup n) (hi : Function.Injective i) (lam : Partition n) :
    RestrictionEligible i.range (ρ.comp (MonoidHom.ofInjective hi).symm.toMonoidHom) lam ↔
      ∃ f : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp i), f ≠ 0 := by
  let e := MonoidHom.ofInjective hi
  constructor
  · rintro ⟨f,hf⟩
    let k := f.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ
      ((spechtRepresentation lam).comp i) (by
        intro g x
        have he := Representation.IntertwiningMap.isIntertwining _ _ f (e g) x
        change f (ρ (e.symm (e g)) x) = spechtRepresentation lam (e g).1 (f x) at he
        rw [e.symm_apply_apply] at he
        change f (ρ g x) = spechtRepresentation lam (i g) (f x) at he
        exact he)
    refine ⟨k,?_⟩
    intro hk
    apply hf
    apply Representation.IntertwiningMap.ext
    change k.toLinearMap = 0
    exact congrArg (fun z : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp i) => z.toLinearMap) hk
  · rintro ⟨f,hf⟩
    let k := f.toLinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ.comp e.symm.toMonoidHom) ((spechtRepresentation lam).comp i.range.subtype) (by
        intro g x
        have he := Representation.IntertwiningMap.isIntertwining _ _ f (e.symm g) x
        change f (ρ (e.symm g) x) = spechtRepresentation lam (i (e.symm g)) (f x) at he
        rwa [MonoidHom.apply_ofInjective_symm] at he)
    refine ⟨k,?_⟩
    intro hk
    apply hf
    apply Representation.IntertwiningMap.ext
    change k.toLinearMap = 0
    exact congrArg (fun z : Representation.IntertwiningMap (ρ.comp e.symm.toMonoidHom) ((spechtRepresentation lam).comp i.range.subtype) => z.toLinearMap) hk

theorem positive_injective_restriction {n : ℕ} (ρ : Representation ℂ G E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (i : G →* SymmetricGroup n) (hi : Function.Injective i)
    (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun g => f (i g)))).re ∧
    (finrank ℂ E : ℝ) * (LinearMap.trace ℂ E (coefficientAction ρ (fun g => f (i g)))).re ≤
      ((Fintype.card G : ℝ) / (Fintype.card (SymmetricGroup n) : ℝ)) *
        ∑ lam : Partition n, if
          (∃ F : Representation.IntertwiningMap ρ ((spechtRepresentation lam).comp i), F ≠ 0) then
          (spechtDimension lam : ℝ) *
            (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re
        else 0 := by
  let : Fintype i.range := @Subgroup.instFintypeSubtypeMemOfDecidablePred _ _ i.range
    (fun _ => Classical.propDecidable _) inferInstance
  let e := MonoidHom.ofInjective hi
  let τ : Representation ℂ i.range E := ρ.comp e.symm.toMonoidHom
  let : τ.IsIrreducible := irreducible_comp_surjective ρ e.symm.toMonoidHom e.symm.surjective
  have ht := specht_positive_restriction i.range τ (fun g => hρ (e.symm g)) f hf
  have he : coefficientAction τ (fun g : i.range => f g) =
      coefficientAction ρ (fun g => f (i g)) := coefficientAction_comp_equiv ρ e _
  erw [he] at ht
  have hc : Fintype.card i.range = Fintype.card G := (Fintype.card_congr e.toEquiv).symm
  simp only [hc, τ, e, restrictionEligible_range_iff] at ht
  exact ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProjectionTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hP : P * P = P) (hcomm : ∀ g, ρ g * P = P * ρ g)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma specht_dimension_expansion {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) :
    finrank ℂ E = ∑ lam : Partition n,
      finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) * spechtDimension lam := by
  have ht := character_specht_expansion ρ 1
  simp only [Representation.char_one] at ht
  exact_mod_cast ht

lemma exists_nonzero_of_multiplicity_ne_zero {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (hm : finrank ℂ (Representation.IntertwiningMap ρ σ) ≠ 0) :
    ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hm (finrank_zero_iff_forall_zero.mpr hn)

theorem sector_positive_restriction_oai {p n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup p) E)
    (i : SymmetricGroup p →* SymmetricGroup n) (hi : Function.Injective i)
    (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (D T : ℝ) (hD : 0 < D) (hT : 0 ≤ T)
    (hdegree : ∀ mu : Partition p,
      (∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) →
        D ≤ spechtDimension mu)
    (hambient : ∀ mu : Partition p,
      (∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) →
      ∀ lam : Partition n,
        (∃ k : Representation.IntertwiningMap (spechtRepresentation mu)
          ((spechtRepresentation lam).comp i), k ≠ 0) →
        (spechtDimension lam : ℝ) *
          (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤ T) :
    (LinearMap.trace ℂ E (coefficientAction ρ (fun g => f (i g)))).re ≤
      (finrank ℂ E : ℝ) *
        (((p.factorial : ℝ) / n.factorial) * (Fintype.card (Partition n) : ℝ) * T) / D^2 := by
  let R := ((p.factorial : ℝ) / n.factorial) * (Fintype.card (Partition n) : ℝ) * T
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hterm (mu : Partition p)
      (hm : finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) ≠ 0) :
      (LinearMap.trace ℂ (Specht mu)
        (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re ≤
        (spechtDimension mu : ℝ) * R / D^2 := by
    have he := exists_nonzero_of_multiplicity_ne_zero _ _ hm
    let := specht_irreducible mu
    have ht := positive_injective_restriction (spechtRepresentation mu)
      (spechtRepresentation_norm mu) i hi f hf
    have hs : (∑ lam : Partition n, if
        (∃ k : Representation.IntertwiningMap (spechtRepresentation mu)
          ((spechtRepresentation lam).comp i), k ≠ 0) then
          (spechtDimension lam : ℝ) *
            (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re
        else 0) ≤ (Fintype.card (Partition n) : ℝ) * T := by
      calc
        _ ≤ ∑ _lam : Partition n, T := by
          apply Finset.sum_le_sum
          intro lam _
          split_ifs with hh
          · exact hambient mu he lam hh
          · exact hT
        _ = _ := by simp
    have hb : (spechtDimension mu : ℝ) *
        (LinearMap.trace ℂ (Specht mu)
          (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re ≤ R := by
      have hb := ht.2.trans (mul_le_mul_of_nonneg_left hs (by positivity))
      simpa only [spechtDimension, SymmetricGroup, Fintype.card_perm, Fintype.card_fin, mul_assoc, R] using hb
    have hdmu : D ≤ (spechtDimension mu : ℝ) := hdegree mu he
    have hdsq : D^2 ≤ (spechtDimension mu : ℝ)^2 := sq_le_sq₀ hD.le (Nat.cast_nonneg _) |>.mpr hdmu
    apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
    calc
      _ = D^2 * (LinearMap.trace ℂ (Specht mu)
          (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re := mul_comm _ _
      _ ≤ (spechtDimension mu : ℝ)^2 * (LinearMap.trace ℂ (Specht mu)
          (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re :=
        mul_le_mul_of_nonneg_right hdsq ht.1
      _ = (spechtDimension mu : ℝ) * ((spechtDimension mu : ℝ) *
          (LinearMap.trace ℂ (Specht mu)
            (coefficientAction (spechtRepresentation mu) (fun g => f (i g)))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
  rw [trace_specht_expansion, Complex.re_sum]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  calc
    _ ≤ ∑ mu : Partition p,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) : ℝ) *
          ((spechtDimension mu : ℝ) * R / D^2) := by
      apply Finset.sum_le_sum
      intro mu _
      by_cases hm : finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) = 0
      · simp [hm]
      · exact mul_le_mul_of_nonneg_left (hterm mu hm) (Nat.cast_nonneg _)
    _ = _ := by
      change (∑ mu : Partition p,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) : ℝ) *
          ((spechtDimension mu : ℝ) * R / D^2)) = (finrank ℂ E : ℝ) * R / D^2
      have hd : (∑ mu : Partition p,
          (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ) : ℝ) *
            (spechtDimension mu : ℝ)) = (finrank ℂ E : ℝ) := by
        exact_mod_cast (specht_dimension_expansion ρ).symm
      simp_rw [mul_div_assoc, ← mul_assoc]
      rw [← Finset.sum_mul, hd]

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.sector_positive_restriction_oai := @OAI.SignedSweeps.sector_positive_restriction_oai
