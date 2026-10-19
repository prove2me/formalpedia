-- Prove2me | solution 1 for OAI.SpinAngle.TypeBlocks.density_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:32:11.637566+00:00
-- url     : https://prove2.me/submissions/5b0be42f-985a-462b-8c64-a6ae93e47f1b

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/Core.lean:L4772-L4811
-- (upload_full_project.md Phase 4): solution for node OAI.SpinAngle.TypeBlocks.density_mixture. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core
import Theorems.Thm_OAI_SpinAngle_CompactMixture_convexHull_compact
import Theorems.Thm_OAI_SpinAngle_EntropyMonomial_sum_log_ratio
import Theorems.Thm_OAI_SpinAngle_SignedCarrier_intertwiner_hermitian

-- ---- from OAI.RepresentationTheory.SpinAngle.Core ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
private theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
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

lemma tensor_hermitian (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    (TensorRep.tensor (fun _ : Cells D => a)).IsHermitian := by
  change star (TensorRep.tensor (fun _ : Cells D => a)) = _
  rw [← TensorRep.tensor_star]
  congr 1
  funext i
  exact ha

lemma hermitianAction_symmetric (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.IsHermitian) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := Carrier D q hq) (hermitianAction D q hq a ha) := by
  intro x y
  rw [← (inclusion D q hq).inner_map_map, ← (inclusion D q hq).inner_map_map x,
    inclusion_hermitianAction, inclusion_hermitianAction]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr (tensor_hermitian D q a ha)) x.val.val y.val.val

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

lemma rep_unitary (g : Group q) (v w : Raw (q := q) (τ := τ)) :
    ⟪rep g v,rep g w⟫_ℂ = ⟪v,w⟫_ℂ := TensorRep.rep_unitary (blockGroup g) v w

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

lemma inner_move
    {G : Type*}
    [contextInstance1640_21 : Group G]
    {E : Type*}
    [contextInstance1641_23 : NormedAddCommGroup E]
    [contextInstance1641_46 : InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E)
    (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ) (g : G) (x y : E) : ⟪x,ρ g y⟫_ℂ = ⟪ρ g⁻¹ x,y⟫_ℂ := by
  have h := hρ g (ρ g⁻¹ x) y
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h

end SpinAngle.UnitaryNaturality

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

variable {τ : Type*} [contextInstance1741_21 : Fintype τ] [contextInstance1741_33 : DecidableEq τ]

end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance1770_23 : Fintype ι] [contextInstance1770_35 : DecidableEq ι] [contextInstance1770_51 : Fintype n] [contextInstance1770_63 : DecidableEq n]

lemma continuous_action (v : EuclideanSpace ℂ (ι → n)) :
    Continuous (fun A : Matrix n n ℂ => action A v) := by
  change Continuous (fun A : Matrix n n ℂ =>
    WithLp.toLp 2 (fun x : ι → n => ∑ y, (∏ i, A (x i) (y i)) * v y))
  apply (PiLp.continuous_toLp 2 (fun _ : ι → n => ℂ)).comp
  fun_prop

lemma continuous_rep : Continuous (fun g : Matrix.unitaryGroup n ℂ =>
    (rep (ι := ι) g).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (continuous_action v).comp continuous_subtype_val
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)
lemma continuous_rep : Continuous (fun g : Matrix.unitaryGroup (Fin q) ℂ =>
    ((ordinary D q hq).toRepresentation g).toContinuousLinearMap) := by
  let : InnerProductSpace ℂ (ordinary D q hq).toSubmodule := carrierInner D q hq
  apply (continuous_clm_apply (𝕜 := ℂ) (E := Carrier D q hq) (F := Carrier D q hq)).mpr
  intro v
  apply (inclusion D q hq).comp_continuous_iff.mp
  change Continuous (fun g : Matrix.unitaryGroup (Fin q) ℂ =>
    TensorRep.rep g (inclusion D q hq v))
  exact continuous_clm_apply.mp (TensorRep.continuous_rep (ι := Cells D) (n := Fin q)) _
end SpinAngle.PolynomialCarrier

namespace SpinAngle.ExternalTensor
open scoped TensorProduct
variable {G H : Type*} [contextInstance1802_23 : Group G] [contextInstance1802_33 : Group H] [contextInstance1802_43 : TopologicalSpace G] [contextInstance1802_64 : TopologicalSpace H]
variable {E F : Type*} [contextInstance1803_23 : NormedAddCommGroup E] [contextInstance1803_46 : InnerProductSpace ℂ E]
  [contextInstance1804_2 : NormedAddCommGroup F] [contextInstance1804_25 : InnerProductSpace ℂ F]
  [contextInstance1805_2 : FiniteDimensional ℂ E] [contextInstance1805_26 : FiniteDimensional ℂ F]
lemma continuous_rep (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (hρ : Continuous (fun g => (ρ g).toContinuousLinearMap))
    (hσ : Continuous (fun h => (σ h).toContinuousLinearMap)) :
    Continuous (fun g : G × H => (rep ρ σ g).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    change Continuous (fun g : G × H => ρ g.1 x ⊗ₜ[ℂ] σ g.2 y)
    exact TensorProduct.continuous_tmul.comp
      (((continuous_clm_apply.mp hρ x).comp continuous_fst).prodMk
        ((continuous_clm_apply.mp hσ y).comp continuous_snd))
  | add x y hx hy =>
    have hh : Continuous (fun g : G × H => (rep ρ σ g).toContinuousLinearMap x +
        (rep ρ σ g).toContinuousLinearMap y) := hx.add hy
    convert hh using 1
    funext g
    exact map_add _ x y
end SpinAngle.ExternalTensor

namespace SpinAngle.SignedTensor
variable {q : ℕ} {τ : Type*} [contextInstance1828_29 : Fintype τ] [contextInstance1828_41 : DecidableEq τ]
lemma continuous_block : Continuous (block (q := q)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : Mat q × Mat q => if i.2 = j.2 then (cond i.2 A.2 A.1) i.1 j.1 else 0)
  split_ifs
  · cases i.2 <;> simp only [Bool.cond_false, Bool.cond_true] <;> fun_prop
  · fun_prop

lemma continuous_blockGroup : Continuous (blockGroup (q := q)) := by
  apply Continuous.subtype_mk
  exact continuous_block.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

lemma continuous_rep : Continuous (fun g : Group q => (rep (τ := τ) g).toContinuousLinearMap) :=
  TensorRep.continuous_rep.comp continuous_blockGroup
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
lemma continuous_rep : Continuous (fun g : Group q => (rep a b q ha hb g).toContinuousLinearMap) :=
  ExternalTensor.continuous_rep _ _ (PolynomialCarrier.continuous_rep a q ha)
    (PolynomialCarrier.continuous_rep b q hb)
end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance1859_23 : Fintype ι] [contextInstance1859_35 : DecidableEq ι] [contextInstance1859_51 : Fintype n] [contextInstance1859_63 : DecidableEq n]
lemma tensor_posSemidef (a : ι → Matrix n n ℂ) (ha : ∀ i, (a i).PosSemidef) :
    (tensor a).PosSemidef := by
  let r : ι → Matrix n n ℂ := fun i => CFC.sqrt (a i)
  have he : tensor a = star (tensor r) * tensor r := by
    rw [← tensor_star, ← tensor_mul]
    congr 1
    funext i
    dsimp [r]
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a i))).star_eq,
      CFC.sqrt_mul_sqrt_self (a i) (ha i).nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma action_positive (a : Matrix n n ℂ) (ha : a.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := EuclideanSpace ℂ (ι → n)) (action a) :=
  Matrix.isPositive_toEuclideanLin_iff.mpr (tensor_posSemidef (fun _ : ι => a) (fun _ => ha))
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical InnerProductSpace
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

lemma hermitianAction_positive (a : Matrix (Fin q) (Fin q) ℂ) (ha : a.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Carrier D q hq) (hermitianAction D q hq a ha.isHermitian) := by
  refine ⟨hermitianAction_symmetric D q hq a ha.isHermitian, ?_⟩
  intro x
  rw [← (inclusion D q hq).inner_map_map, inclusion_hermitianAction]
  exact (TensorRep.action_positive a ha).2 (inclusion D q hq x)

lemma highestVector_ne_zero : highestVector D q hq ≠ 0 := by
  intro h
  have he := congrArg (inclusion D q hq) h
  exact highest_ne_zero D q hq (by simpa [highestVector] using he)

lemma inclusion_linear_hermitianAction (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.IsHermitian)
    (v : Carrier D q hq) :
    (inclusion D q hq).toLinearMap (hermitianAction D q hq A hA v) =
      TensorRep.action A ((inclusion D q hq).toLinearMap v) :=
  inclusion_hermitianAction D q hq A hA v

lemma highestVector_diagonal (t : Fin q → ℝ) :
    hermitianAction D q hq (Matrix.diagonal (fun i => (t i : ℂ)))
      (Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])) (highestVector D q hq) =
        (highestMonomial D q hq t : ℂ) • highestVector D q hq := by
  have hinj : Function.Injective (inclusion D q hq).toLinearMap := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply hinj
  rw [inclusion_linear_hermitianAction, map_smul]
  change TensorRep.action (Matrix.diagonal (fun i => (t i : ℂ))) (highest D q hq) =
    (highestMonomial D q hq t : ℂ) • highest D q hq
  rw [highest_diagonal]
  congr 1
  exact (map_prod Complex.ofRealHom _ _).symm

lemma card_rowColor (j : Fin q) :
    (Finset.univ.filter fun i : Cells D => rowColor D q hq i = j).card = D.rowLen j := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {i : Cells D // rowColor D q hq i = j} = Fintype.card {i : Cells D // i.val.1 = j.val} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun i => Fin.ext_iff))
    _ = D.rowLen j := card_row_subtype D j

lemma highestMonomial_eq_rowLen (t : Fin q → ℝ) :
    highestMonomial D q hq t = ∏ j : Fin q, t j ^ D.rowLen j := by
  unfold highestMonomial
  rw [← Finset.prod_fiberwise' Finset.univ (rowColor D q hq) t]
  simp only [Finset.prod_const, card_rowColor]

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
namespace SpinAngle.TensorPositive
variable {E F : Type*} [contextInstance1947_23 : NormedAddCommGroup E] [contextInstance1947_46 : InnerProductSpace ℂ E]
  [contextInstance1948_2 : NormedAddCommGroup F] [contextInstance1948_25 : InnerProductSpace ℂ F]
  [contextInstance1949_2 : FiniteDimensional ℂ E] [contextInstance1949_26 : FiniteDimensional ℂ F]

lemma mapL_nonneg (A : E →L[ℂ] E) (B : F →L[ℂ] F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ TensorProduct.mapL A B := by
  let a := CFC.sqrt A
  let b := CFC.sqrt B
  have ha : star a = a := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hb : star b = b := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  have hstar : star (TensorProduct.mapL a b) = TensorProduct.mapL a b := by
    change ContinuousLinearMap.adjoint (TensorProduct.mapL a b) = _
    rw [TensorProduct.adjoint_mapL]
    change TensorProduct.mapL (star a) (star b) = _
    rw [ha,hb]
  have he : star (TensorProduct.mapL a b) * TensorProduct.mapL a b = TensorProduct.mapL A B := by
    rw [hstar, ← TensorProduct.mapL_mul]
    dsimp [a,b]
    rw [CFC.sqrt_mul_sqrt_self A hA, CFC.sqrt_mul_sqrt_self B hB]
  rw [← he]
  exact star_mul_self_nonneg _

lemma map_positive (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (hA : A.IsPositive) (hB : B.IsPositive) :
    (TensorProduct.map A B).IsPositive := by
  have ha : 0 ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hA
  have hb : 0 ≤ B.toContinuousLinearMap :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hB
  have h := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (mapL_nonneg _ _ ha hb)
  change ((TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap).toLinearMap).IsPositive at h
  simpa only [TensorProduct.toLinearMap_mapL, LinearMap.coe_toContinuousLinearMap] using h

end SpinAngle.TensorPositive

noncomputable section
open scoped BigOperators
namespace SpinAngle.EntropyMonomial
variable {ι : Type*} [contextInstance2001_21 : Fintype ι]

lemma optimal_prod (n : ι → ℕ) (p : ℕ) (hp : 0 < p) (hn : ∑ i, n i = p) :
    ∏ i, ((n i : ℝ) / p) ^ n i = Real.exp (-entropy n) := by
  rw [← sum_log_ratio n p hp hn, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : n i = 0
  · simp [hi]
  have hpos : 0 < (n i : ℝ) / p := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast hp)
  rw [Real.exp_nat_mul, Real.exp_log hpos]

end SpinAngle.EntropyMonomial

noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators
namespace SpinAngle.PositiveTrace
variable {E : Type*} [contextInstance2090_21 : NormedAddCommGroup E] [contextInstance2090_44 : InnerProductSpace ℂ E]
  [contextInstance2091_2 : FiniteDimensional ℂ E]

lemma eigenvalues_nonneg (A : E →ₗ[ℂ] E) (hA : A.IsPositive)
    (i : Fin (Module.finrank ℂ E)) : 0 ≤ hA.isSymmetric.eigenvalues rfl i := by
  have h := hA.inner_nonneg_right (hA.isSymmetric.eigenvectorBasis rfl i)
  rw [hA.isSymmetric.apply_eigenvectorBasis rfl i, inner_smul_right,
    (hA.isSymmetric.eigenvectorBasis rfl).inner_eq_one] at h
  simpa only [mul_one, RCLike.ofReal_nonneg] using h

theorem eigenvalue_le_trace (A : E →ₗ[ℂ] E) (hA : A.IsPositive)
    (v : E) (hv : v ≠ 0) (t : ℝ) (he : A v = (t : ℂ) • v) :
    t ≤ (LinearMap.trace ℂ E A).re := by
  classical
  let b := hA.isSymmetric.eigenvectorBasis rfl
  have hcoord : ∃ i, b.repr v i ≠ 0 := by
    by_contra! hh
    apply hv
    apply b.repr.injective
    ext i
    simpa using hh i
  obtain ⟨i,hi⟩ := hcoord
  have h := congrArg (fun x : E => b.repr x i) he
  rw [hA.isSymmetric.eigenvectorBasis_apply_self_apply, map_smul, PiLp.smul_apply,
    smul_eq_mul] at h
  have ht : hA.isSymmetric.eigenvalues rfl i = t := by
    exact Complex.ofReal_injective (mul_right_cancel₀ hi h)
  change t ≤ RCLike.re (LinearMap.trace ℂ E A)
  rw [hA.isSymmetric.re_trace_eq_sum_eigenvalues rfl, ← ht]
  exact Finset.single_le_sum (fun j _ => eigenvalues_nonneg A hA j) (Finset.mem_univ i)

end SpinAngle.PositiveTrace

noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder
namespace SpinAngle.Isotypic
variable {G : Type*} [contextInstance2131_21 : Group G]
variable {E F : Type*} [contextInstance2132_23 : NormedAddCommGroup E] [contextInstance2132_46 : InnerProductSpace ℂ E]
  [contextInstance2133_2 : NormedAddCommGroup F] [contextInstance2133_25 : InnerProductSpace ℂ F]
  [contextInstance2134_2 : FiniteDimensional ℂ E] [contextInstance2134_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)

lemma scalar_on_space
    {G : Type*}
    [contextInstance2131_21 : Group G]
    {E : Type*} {F : Type*}
    [contextInstance2132_23 : NormedAddCommGroup E]
    [contextInstance2132_46 : InnerProductSpace ℂ E]
    [contextInstance2133_2 : NormedAddCommGroup F]
    [contextInstance2133_25 : InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F) (A : F →ₗ[ℂ] F) (c : ℂ)
    (h : ∀ f : ρ.IntertwiningMap σ, ∀ x, A (f x) = c • f x)
    (v : F) (hv : v ∈ space ρ σ) : A v = c • v := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨⟨f,x⟩,rfl⟩ := hv; exact h f x
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy, smul_add]
  | smul z x hx ih => simp [ih, smul_comm c z]

end SpinAngle.Isotypic

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

lemma hermitianAction_positive (A : Mat q × Mat q) (hA : A.1.PosSemidef) (hB : A.2.PosSemidef) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Carrier a b q ha hb)
      (hermitianAction a b q ha hb A hA.isHermitian hB.isHermitian) :=
  TensorPositive.map_positive (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb) _ _
    (PolynomialCarrier.hermitianAction_positive a q ha A.1 hA)
    (PolynomialCarrier.hermitianAction_positive b q hb A.2 hB)

end SpinAngle.SignedCarrier

namespace SpinAngle.EntropyMonomial
open scoped BigOperators
variable {ι : Type*} [contextInstance2379_21 : Fintype ι] [contextInstance2379_33 : Nonempty ι]

lemma exists_optimal (n : ι → ℕ) : ∃ t : ι → ℝ,
    (∀ i, 0 ≤ t i) ∧ (∑ i, t i = 1) ∧ (∏ i, t i ^ n i = Real.exp (-entropy n)) := by
  classical
  let p := ∑ i, n i
  by_cases hp : p = 0
  · have hn : ∀ i, n i = 0 := by
      intro i
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (n j)) (Finset.mem_univ i)
      change n i ≤ p at h
      omega
    let i₀ := Classical.choice (inferInstance : Nonempty ι)
    refine ⟨fun i => if i = i₀ then 1 else 0, ?_, ?_, ?_⟩
    · intro i; dsimp only; split_ifs <;> norm_num
    · simp
    · simp [hn, entropy]
  · refine ⟨fun i => (n i : ℝ) / p, fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_, ?_⟩
    · rw [← Finset.sum_div]
      have he : ∑ i, (n i : ℝ) = p := by simp [p]
      rw [he, div_self (by exact_mod_cast hp)]
    · exact optimal_prod n p (Nat.pos_of_ne_zero hp) rfl
end SpinAngle.EntropyMonomial

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance2407_21 : Fintype τ] [contextInstance2407_33 : DecidableEq τ]

lemma highestVector_ne_zero : highestVector a b q ha hb ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [highestVector, TensorProduct.norm_tmul (E := PolynomialCarrier.Carrier a q ha)
    (F := PolynomialCarrier.Carrier b q hb), norm_zero] at hn
  exact (mul_ne_zero (norm_ne_zero_iff.mpr (PolynomialCarrier.highestVector_ne_zero a q ha))
    (norm_ne_zero_iff.mpr (PolynomialCarrier.highestVector_ne_zero b q hb))) hn

lemma highestVector_diagonal (t : Fin q ⊕ Fin q → ℝ) :
    hermitianAction a b q ha hb
      (Matrix.diagonal (fun i => (t (.inl i) : ℂ)), Matrix.diagonal (fun i => (t (.inr i) : ℂ)))
      (Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint]))
      (Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint]))
      (highestVector a b q ha hb) =
        ((∏ i, t i ^ parts a b q i : ℝ) : ℂ) • highestVector a b q ha hb := by
  rw [hermitianAction, highestVector, TensorProduct.map_tmul,
    PolynomialCarrier.highestVector_diagonal, PolynomialCarrier.highestVector_diagonal,
    TensorProduct.smul_tmul_smul, PolynomialCarrier.highestMonomial_eq_rowLen,
    PolynomialCarrier.highestMonomial_eq_rowLen]
  congr 1
  rw [Fintype.prod_sum_type, Complex.ofReal_mul]
  rfl

lemma exists_density_trace_lower [Nonempty (Fin q)] : ∃ (A : Mat q × Mat q) (hA : IsEvenDensity A),
    Real.exp (-entropy a b q) ≤
      (LinearMap.trace ℂ (Carrier a b q ha hb)
        (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)).re := by
  obtain ⟨t,ht,hs,he⟩ := EntropyMonomial.exists_optimal (parts a b q)
  let A : Mat q × Mat q :=
    (Matrix.diagonal (fun i => (t (.inl i) : ℂ)), Matrix.diagonal (fun i => (t (.inr i) : ℂ)))
  have hA : IsEvenDensity A := by
    refine ⟨Matrix.PosSemidef.diagonal (fun i => by simpa using ht (.inl i)),
      Matrix.PosSemidef.diagonal (fun i => by simpa using ht (.inr i)), ?_⟩
    simp only [A, Matrix.trace_diagonal]
    have hh := congrArg Complex.ofReal hs
    simpa only [Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_one] using hh
  refine ⟨A,hA,?_⟩
  apply PositiveTrace.eigenvalue_le_trace _ (hermitianAction_positive a b q ha hb A hA.1 hA.2.1)
    (highestVector a b q ha hb) (highestVector_ne_zero a b q ha hb)
  have h := highestVector_diagonal a b q ha hb t
  rw [he] at h
  exact h
end SpinAngle.SignedCarrier

noncomputable section
open scoped BigOperators
namespace SpinAngle.DenseLU

end SpinAngle.DenseLU

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier
noncomputable section
open scoped BigOperators
namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable (σ : Type*) [contextInstance2689_21 : Fintype σ] [contextInstance2689_33 : DecidableEq σ] (p : ℕ)

variable {q : ℕ}
end SpinAngle.PolyDimension

namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable {σ X : Type*} [contextInstance2737_23 : Fintype σ] [contextInstance2737_35 : DecidableEq σ] [contextInstance2737_51 : Fintype X] (p : ℕ)

end SpinAngle.PolyDimension

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young PolyDimension MvPolynomial
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
namespace SpinAngle.CompactTwirl

variable {G : Type*} [contextInstance2861_21 : Group G] [contextInstance2861_31 : TopologicalSpace G] [contextInstance2861_52 : IsTopologicalGroup G]
  [contextInstance2862_2 : CompactSpace G] [contextInstance2862_19 : MeasurableSpace G] [contextInstance2862_39 : BorelSpace G]

lemma continuous_integrable {A : Type*} [NormedAddCommGroup A] (f : G → A)
    (hf : Continuous f) : Integrable f (compactHaar (G := G)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

variable {A : Type*} [contextInstance2877_21 : NormedRing A] [contextInstance2877_36 : NormedAlgebra ℝ A] [contextInstance2877_56 : CompleteSpace A]

lemma continuous_conjugate
    {G : Type*}
    [contextInstance2861_21 : Group G]
    [contextInstance2861_31 : TopologicalSpace G]
    [contextInstance2861_52 : IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {A : Type*}
    [contextInstance2877_21 : NormedRing A]
    [NormedAlgebra ℝ A]
    [CompleteSpace A] (ρ : G →* A) (hρ : Continuous ρ) (a : A) :
    Continuous (conjugate ρ a) :=
  (hρ.mul continuous_const).mul (hρ.comp continuous_inv)

lemma integrable_conjugate (ρ : G →* A) (hρ : Continuous ρ) (a : A) :
    Integrable (conjugate ρ a) compactHaar :=
  continuous_integrable _ (continuous_conjugate ρ hρ a)

lemma conjugate_mul
    {G : Type*}
    [contextInstance2861_21 : Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {A : Type*}
    [contextInstance2877_21 : NormedRing A]
    [NormedAlgebra ℝ A]
    [CompleteSpace A] (ρ : G →* A) (a : A) (g h : G) :
    conjugate ρ a (g * h) = ρ g * conjugate ρ a h * ρ g⁻¹ := by
  simp only [conjugate, mul_inv_rev, map_mul, mul_assoc]

lemma twirl_commute (ρ : G →* A) (hρ : Continuous ρ) (a : A) (g : G) :
    Commute (ρ g) (twirl ρ a) := by
  have hi := integrable_conjugate ρ hρ a
  have hinv : (ρ g⁻¹) * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have he : ρ g * twirl ρ a * ρ g⁻¹ = twirl ρ a := by
    rw [twirl, ← integral_const_mul_of_integrable hi]
    rw [← integral_mul_const_of_integrable (hi.const_mul _)]
    simp_rw [← conjugate_mul]
    exact integral_mul_left_eq_self _ g
  have hc := congrArg (fun x : A => x * ρ g) he
  simpa only [Commute, SemiconjBy, mul_assoc, hinv, mul_one] using hc

lemma twirl_trace (τ : A →L[ℝ] ℂ) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    (ρ : G →* A) (hρ : Continuous ρ) (a : A) : τ (twirl ρ a) = τ a := by
  rw [twirl, ← τ.integral_comp_comm (integrable_conjugate ρ hρ a)]
  have he (g : G) : τ (conjugate ρ a g) = τ a := by
    rw [conjugate, hτ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp [he, integral_const, measureReal_def]

section Positivity
variable [contextInstance2919_9 : PartialOrder A] [contextInstance2919_26 : IsOrderedAddMonoid A] [contextInstance2919_49 : StarRing A] [contextInstance2919_62 : StarOrderedRing A]
  [contextInstance2920_2 : ClosedIciTopology A] [contextInstance2920_24 : IsOrderedModule ℝ A]

lemma twirl_nonneg
    {G : Type*}
    [contextInstance2861_21 : Group G]
    [contextInstance2861_31 : TopologicalSpace G]
    [contextInstance2861_52 : IsTopologicalGroup G]
    [contextInstance2862_2 : CompactSpace G]
    [contextInstance2862_19 : MeasurableSpace G]
    [contextInstance2862_39 : BorelSpace G]
    {A : Type*}
    [contextInstance2877_21 : NormedRing A]
    [contextInstance2877_36 : NormedAlgebra ℝ A]
    [CompleteSpace A]
    [contextInstance2919_9 : PartialOrder A]
    [contextInstance2919_26 : IsOrderedAddMonoid A]
    [contextInstance2919_49 : StarRing A]
    [contextInstance2919_62 : StarOrderedRing A]
    [contextInstance2920_2 : ClosedIciTopology A]
    [contextInstance2920_24 : IsOrderedModule ℝ A] (ρ : G →* A) (a : A)
    (hρ : ∀ g, ρ g⁻¹ = star (ρ g)) (ha : 0 ≤ a) : 0 ≤ twirl ρ a := by
  apply integral_nonneg
  intro g
  dsimp [conjugate]
  rw [hρ]
  exact star_right_conjugate_nonneg ha _
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

lemma operatorTrace_mul_comm
    {G : Type*}
    [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance2951_21 : NormedAddCommGroup E]
    [contextInstance2951_44 : InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (a b : E →L[ℂ] E) :
    operatorTrace (a * b) = operatorTrace (b * a) :=
  LinearMap.trace_mul_comm ℂ a.toLinearMap b.toLinearMap

theorem twirl_irreducible (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (hρ : Continuous (continuousAction ρ)) (a : E →L[ℂ] E) :
    twirl (continuousAction ρ) a =
      (operatorTrace a / (Module.finrank ℂ E : ℂ)) • (1 : E →L[ℂ] E) := by
  let t := twirl (continuousAction ρ) a
  let f : ρ.IntertwiningMap ρ :=
    t.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (by
      intro g v
      have h := twirl_commute (continuousAction ρ) hρ a g
      exact (congrArg (fun L : E →L[ℂ] E => L v) h.eq).symm)
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective f
  have ht : t = z • (1 : E →L[ℂ] E) := by
    ext v
    exact (congrArg (fun L : ρ.IntertwiningMap ρ => L v) hz).symm
  have htr : operatorTrace t = operatorTrace a :=
    twirl_trace (operatorTrace.restrictScalars ℝ) (operatorTrace_mul_comm (G := G))
      (continuousAction ρ) hρ a
  let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hn : (Module.finrank ℂ E : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have hz' : z = operatorTrace a / (Module.finrank ℂ E : ℂ) := by
    apply (eq_div_iff hn).mpr
    rw [ht, map_smul] at htr
    simpa [operatorTrace_apply (G := G), LinearMap.trace_one] using htr
  simpa only [hz'] using ht

end SpinAngle.CompactTwirl

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3008_21 : Group G] [contextInstance3008_31 : TopologicalSpace G] [contextInstance3008_52 : IsTopologicalGroup G]
  [contextInstance3009_2 : CompactSpace G] [contextInstance3009_19 : MeasurableSpace G] [contextInstance3009_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3010_23 : NormedAddCommGroup E] [contextInstance3010_46 : InnerProductSpace ℂ E]
  [contextInstance3011_2 : NormedAddCommGroup F] [contextInstance3011_25 : InnerProductSpace ℂ F]
  [contextInstance3012_2 : FiniteDimensional ℂ E] [contextInstance3012_26 : FiniteDimensional ℂ F]

lemma twirl_natural (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (hρ : Continuous (continuousAction ρ)) (hσ : Continuous (continuousAction σ))
    (a : E →L[ℂ] E) (A : F →L[ℂ] F) (L : ρ.IntertwiningMap σ)
    (hnat : ∀ x, A (L x) = L (a x)) (x : E) :
    twirl (continuousAction σ) A (L x) = L (twirl (continuousAction ρ) a x) := by
  have hi := integrable_conjugate (continuousAction ρ) hρ a
  have hI := integrable_conjugate (continuousAction σ) hσ A
  rw [twirl, ContinuousLinearMap.integral_apply hI, twirl, ContinuousLinearMap.integral_apply hi]
  change _ = L.toLinearMap.toContinuousLinearMap (∫ g, conjugate (continuousAction ρ) a g x ∂compactHaar)
  rw [← ContinuousLinearMap.integral_comp_comm _ (hi.apply_continuousLinearMap x)]
  apply integral_congr_ae
  filter_upwards [] with g
  change σ g (A (σ g⁻¹ (L x))) = L (ρ g (a (ρ g⁻¹ x)))
  rw [← L.isIntertwining, hnat, L.isIntertwining]

lemma continuousAction_inverse_star
    {G : Type*}
    [contextInstance3008_21 : Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G]
    [MeasurableSpace G]
    [BorelSpace G]
    {E : Type*}
    [contextInstance3010_23 : NormedAddCommGroup E]
    [contextInstance3010_46 : InnerProductSpace ℂ E]
    [contextInstance3012_2 : FiniteDimensional ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ) (g : G) :
    continuousAction ρ g⁻¹ = star (continuousAction ρ g) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change ⟪y,ρ g⁻¹ x⟫_ℂ = ⟪y,(continuousAction ρ g).adjoint x⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right]
  simpa only [inv_inv, continuousAction_apply] using (UnitaryNaturality.inner_move ρ hρ g⁻¹ y x)

end SpinAngle.CompactTwirl

namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3043_21 : CStarAlgebra A] [contextInstance3043_38 : PartialOrder A] [contextInstance3043_55 : StarOrderedRing A]
  [contextInstance3044_2 : NonnegSpectrumClass ℝ A]

lemma scalar_projection_le (T P : A) (hT : 0 ≤ T) (hP : IsStarProjection P)
    (c : ℝ) (he : T * P = c • P) : c • P ≤ T := by
  have hstar := congrArg star he
  have hpT : P * T = c • P := by
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg hT).star_eq,
      star_smul, star_trivial] using hstar
  have hc : Commute (1-P) T := by
    dsimp [Commute,SemiconjBy]
    rw [sub_mul,mul_sub,one_mul,mul_one,hpT,he]
  have hn := hc.mul_nonneg (sub_nonneg.mpr hP.le_one) hT
  rw [sub_mul,one_mul,hpT] at hn
  exact sub_nonneg.mp hn
end SpinAngle.ProjectionOrder

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3062_21 : Group G] [contextInstance3062_31 : TopologicalSpace G] [contextInstance3062_52 : IsTopologicalGroup G]
  [contextInstance3063_2 : CompactSpace G] [contextInstance3063_19 : MeasurableSpace G] [contextInstance3063_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3064_23 : NormedAddCommGroup E] [contextInstance3064_46 : InnerProductSpace ℂ E]
  [contextInstance3065_2 : NormedAddCommGroup F] [contextInstance3065_25 : InnerProductSpace ℂ F]
  [contextInstance3066_2 : FiniteDimensional ℂ E] [contextInstance3066_26 : FiniteDimensional ℂ F]

lemma isotypic_twirl_scalar (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (σ : Representation ℂ G F)
    (hρ : Continuous (continuousAction ρ)) (hσ : Continuous (continuousAction σ))
    (a : E →L[ℂ] E) (A : F →L[ℂ] F)
    (hnat : ∀ L : ρ.IntertwiningMap σ, ∀ x, A (L x) = L (a x)) :
    twirl (continuousAction σ) A * Isotypic.projection ρ σ =
      (operatorTrace a / (Module.finrank ℂ E : ℂ)) • Isotypic.projection ρ σ := by
  ext v
  apply Isotypic.scalar_on_space ρ σ
    (twirl (continuousAction σ) A).toLinearMap
    (operatorTrace a / (Module.finrank ℂ E : ℂ))
  · intro L x
    change twirl (continuousAction σ) A (L x) = _
    rw [twirl_natural ρ σ hρ hσ a A L (hnat L), twirl_irreducible ρ hρ a]
    simp only [smul_apply, one_apply_eq_self, map_smul]
  · exact (Isotypic.space ρ σ).toSubmodule.starProjection_apply_mem v

lemma isotypic_twirl_lower (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    (σ : Representation ℂ G F)
    (hρ : Continuous (continuousAction ρ)) (hσ : Continuous (continuousAction σ))
    (hσunit : ∀ g x y, ⟪σ g x,σ g y⟫_ℂ = ⟪x,y⟫_ℂ)
    (a : E →L[ℂ] E) (A : F →L[ℂ] F) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hnat : ∀ L : ρ.IntertwiningMap σ, ∀ x, A (L x) = L (a x)) :
    ((operatorTrace a).re / (Module.finrank ℂ E : ℝ)) • Isotypic.projection ρ σ ≤
      twirl (continuousAction σ) A := by
  apply ProjectionOrder.scalar_projection_le _ _
    (twirl_nonneg _ A (continuousAction_inverse_star σ hσunit) hA)
    (isStarProjection_starProjection (U := (Isotypic.space ρ σ).toSubmodule))
  have ht : operatorTrace a = ((operatorTrace a).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (LinearMap.IsPositive.trace_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp ha))
  have h := isotypic_twirl_scalar ρ σ hρ hσ a A hnat
  rw [ht] at h
  convert h using 1 <;> simp only [Isotypic.projection,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  change (((operatorTrace a).re / (Module.finrank ℂ E : ℝ) : ℝ) : ℂ) = _
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]

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

lemma twirl_finite_mixture (ρ : Representation ℂ G E)
    (hρ : Continuous (continuousAction ρ)) (a : E →L[ℂ] E) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (g : ι → G),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      twirl (continuousAction ρ) a = ∑ i, w i • conjugate (continuousAction ρ) a (g i) := by
  let f := conjugate (continuousAction ρ) a
  have hf : Continuous f := continuous_conjugate _ hρ a
  have hc : IsCompact (Set.range f) := isCompact_range hf
  have hm : twirl (continuousAction ρ) a ∈ convexHull ℝ (Set.range f) :=
    (convex_convexHull ℝ _).integral_mem (CompactMixture.convexHull_compact hc).isClosed
      (Filter.Eventually.of_forall fun g => subset_convexHull ℝ _ (Set.mem_range_self g))
      (integrable_conjugate _ hρ a)
  obtain ⟨ι,hι,w,z,hw,hs,hz,he⟩ := mem_convexHull_iff_exists_fintype.mp hm
  let := hι
  choose g hg using hz
  refine ⟨ι,hι,w,g,hw,hs,?_⟩
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hg i]
end SpinAngle.CompactTwirl

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

lemma dimension_pos : 0 < dimension a b q ha hb := by
  have : Nontrivial (Carrier a b q ha hb) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Group q))
    (rep a b q ha hb).asModule
  exact Module.finrank_pos

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

lemma conjugateDensity_isEvenDensity (g : Group q) (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    IsEvenDensity (conjugateDensity g A) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.nonneg_iff_posSemidef.mp (star_right_conjugate_nonneg hA.1.nonneg g.1.val)
  · exact Matrix.nonneg_iff_posSemidef.mp (star_right_conjugate_nonneg hA.2.1.nonneg g.2.val)
  · change (g.1.val * A.1 * star g.1.val).trace + (g.2.val * A.2 * star g.2.val).trace = 1
    rw [Matrix.trace_mul_cycle, g.1.property.1, one_mul,
      Matrix.trace_mul_cycle, g.2.property.1, one_mul]
    exact hA.2.2

lemma block_conjugateDensity (g : Group q) (A : Mat q × Mat q) :
    block (conjugateDensity g A) = (blockGroup g).val * block A * (blockGroup g⁻¹).val := by
  change block (((g.1.val,g.2.val) * A) * star (g.1.val,g.2.val)) = _
  rw [map_mul, map_mul, block_star, map_inv]
  rfl

variable {τ : Type*} [contextInstance3254_21 : Fintype τ] [contextInstance3254_33 : DecidableEq τ]
lemma tensor_conjugateDensity (g : Group q) (A : Mat q × Mat q) :
    LinearMap.toContinuousLinearMap (TensorRep.action (ι := τ) (block (conjugateDensity g A))) =
      CompactTwirl.conjugate (CompactTwirl.continuousAction (rep (τ := τ)))
        (LinearMap.toContinuousLinearMap (TensorRep.action (block A))) g := by
  apply ContinuousLinearMap.ext
  intro v
  change TensorRep.action (block (conjugateDensity g A)) v =
    TensorRep.action (blockGroup g).val (TensorRep.action (block A)
      (TensorRep.action (blockGroup g⁻¹).val v))
  rw [block_conjugateDensity, map_mul, map_mul]
  rfl
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
lemma twirl_lower (A : Mat q × Mat q) (hA : IsEvenDensity A) :
    ((LinearMap.trace ℂ (Carrier a b q ha hb)
      (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian)).re /
        (dimension a b q ha hb : ℝ)) • typeProjection (τ := τ) a b q ha hb ≤
    twirl (continuousAction (SignedTensor.rep (q := q) (τ := τ)))
      (LinearMap.toContinuousLinearMap (TensorRep.action (block A))) := by
  exact isotypic_twirl_lower (E := Carrier a b q ha hb) (F := Raw (q := q) (τ := τ))
    (rep a b q ha hb) SignedTensor.rep
    (continuous_rep a b q ha hb) SignedTensor.continuous_rep SignedTensor.rep_unitary
    (LinearMap.toContinuousLinearMap (hermitianAction a b q ha hb A hA.1.isHermitian hA.2.1.isHermitian))
    (LinearMap.toContinuousLinearMap (TensorRep.action (block A)))
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (hermitianAction_positive a b q ha hb A hA.1 hA.2.1))
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (TensorRep.action_positive (block A) (block_posSemidef A hA.1 hA.2.1)))
    (fun L x => (intertwiner_hermitian a b q ha hb L A hA.1.isHermitian hA.2.1.isHermitian x).symm)
end SpinAngle.SignedCarrier

noncomputable section
namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3309_21 : CStarAlgebra A] [contextInstance3309_38 : PartialOrder A] [contextInstance3309_55 : StarOrderedRing A]

lemma rescale_trace_lower (P B : A) (hP : 0 ≤ P) (F t d : ℝ) (hd : 0 < d)
    (ht : Real.exp (-F) ≤ t) (h : (t / d) • P ≤ B) :
    P ≤ (Real.exp F * d) • B := by
  have hbase : (Real.exp (-F) / d) • P ≤ B :=
    (smul_le_smul_of_nonneg_right (div_le_div_of_nonneg_right ht hd.le) hP).trans h
  have hs := smul_le_smul_of_nonneg_left hbase (mul_pos (Real.exp_pos F) hd).le
  have he : (Real.exp F * d) * (Real.exp (-F) / d) = 1 := by
    rw [← mul_div_assoc, mul_right_comm, mul_div_cancel_right₀ _ hd.ne', ← Real.exp_add]
    simp
  simpa only [smul_smul, he, one_smul] using hs
end SpinAngle.ProjectionOrder

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3325_21 : Fintype n] [contextInstance3325_33 : DecidableEq n]
lemma inverse_mono (a b : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (h : a ≤ b) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm a ≤ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm b := by
  apply sub_nonneg.mp
  rw [← map_sub]
  exact map_nonneg (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (sub_nonneg.mpr h)
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3337_21 : Fintype τ] [contextInstance3337_33 : DecidableEq τ] [contextInstance3337_49 : Nonempty (Fin q)]

theorem exists_density_mixture :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (R : ι → Mat q × Mat q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, IsEvenDensity (R i)) ∧
      typeProjection (τ := τ) a b q ha hb ≤
        (Real.exp (entropy a b q) * (dimension a b q ha hb : ℝ)) •
          ∑ i, w i • LinearMap.toContinuousLinearMap (TensorRep.action (block (R i))) := by
  obtain ⟨A,hA,htr⟩ := exists_density_trace_lower a b q ha hb
  obtain ⟨ι,hι,w,g,hw,hs,he⟩ := twirl_finite_mixture
    (SignedTensor.rep (q := q) (τ := τ)) SignedTensor.continuous_rep
    (LinearMap.toContinuousLinearMap (TensorRep.action (block A)))
  let := hι
  refine ⟨ι,hι,w,fun i => conjugateDensity (g i) A,hw,hs,
    fun i => conjugateDensity_isEvenDensity (g i) A hA,?_⟩
  have hh := twirl_lower (τ := τ) a b q ha hb A hA
  have hbound := ProjectionOrder.rescale_trace_lower _ _
    (projection_isStarProjection (τ := τ) a b q ha hb).nonneg (entropy a b q)
    _ (dimension a b q ha hb : ℝ) (by exact_mod_cast dimension_pos a b q ha hb) htr hh
  rw [he] at hbound
  simpa only [tensor_conjugateDensity] using hbound
end SpinAngle.SignedCarrier

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3364_21 : Fintype n] [contextInstance3364_33 : DecidableEq n]
local notation "Φ" => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
lemma inverse_real_smul (r : ℝ) (a : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    (Φ).symm (r • a) = r • (Φ).symm a := by
  change (Φ).symm ((r : ℂ) • a) = (r : ℂ) • (Φ).symm a
  exact map_smul (Φ).symm _ _

lemma inverse_toContinuous (a : Matrix n n ℂ) :
    (Φ).symm (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin a)) = a := by
  exact (Φ).symm_apply_apply a
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

lemma inverse_action (A : Matrix (Spin q) (Spin q) ℂ) :
    (Matrix.toEuclideanCLM (n := τ → Spin q) (𝕜 := ℂ)).symm
      (LinearMap.toContinuousLinearMap (TensorRep.action A)) = TensorRep.tensor (fun _ : τ => A) :=
  MatrixBridge.inverse_toContinuous _

variable [contextInstance3441_9 : Nonempty (Fin q)]

theorem exists_matrix_density_mixture :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (R : ι → Mat q × Mat q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, IsEvenDensity (R i)) ∧
      matrixProjection (τ := τ) a b q ha hb ≤
        (Real.exp (entropy a b q) * (dimension a b q ha hb : ℝ)) •
          ∑ i, w i • TensorRep.tensor (fun _ : τ => block (R i)) := by
  obtain ⟨ι,hι,w,R,hw,hs,hR,hdom⟩ := exists_density_mixture (τ := τ) a b q ha hb
  let := hι
  refine ⟨ι,hι,w,R,hw,hs,hR,?_⟩
  have h := MatrixBridge.inverse_mono _ _ hdom
  simpa only [MatrixBridge.inverse_real_smul, map_sum, inverse_action, matrixProjection] using h
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

end SpinAngle

namespace SpinAngle
open scoped BigOperators
variable {ι : Type*} [contextInstance3841_21 : Fintype ι] [contextInstance3841_33 : DecidableEq ι]

variable {R C : Type*} [contextInstance3877_23 : Fintype R] [contextInstance3877_35 : DecidableEq R] [contextInstance3877_51 : Fintype C] [contextInstance3877_63 : DecidableEq C]

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

lemma tensor_star
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [DecidableEq ι]
    {ν : ι → Type*}
    [∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] (A : ∀ i, Mat (ν i)) : tensor (fun i => star (A i)) = star (tensor A) := by
  ext x y
  simp [tensor, Matrix.star_apply]

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

lemma tensor_nonneg (A : ∀ i, Mat (ν i)) (hA : ∀ i, 0 ≤ A i) : 0 ≤ tensor A := by
  have he : tensor A = star (tensor (fun i => CFC.sqrt (A i))) * tensor (fun i => CFC.sqrt (A i)) := by
    rw [← tensor_star, ← tensor_mul]
    congr 1
    funext i
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (A i))).star_eq,
      CFC.sqrt_mul_sqrt_self (A i) (hA i)]
  rw [he]
  exact star_mul_self_nonneg _

lemma tensor_sum
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [contextInstance4012_33 : DecidableEq ι]
    {ν : ι → Type*}
    [∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (A : ∀ i, κ i → Mat (ν i)) :
    tensor (fun i => ∑ k, A i k) = ∑ f : ∀ i, κ i, tensor (fun i => A i (f i)) := by
  ext x y
  simp only [tensor, Matrix.sum_apply]
  exact (Fintype.prod_sum (fun i (k : κ i) => A i k (x i) (y i)))

lemma tensor_smul
    {ι : Type*}
    [contextInstance4012_21 : Fintype ι]
    [DecidableEq ι]
    {ν : ι → Type*}
    [∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (ν i)] (w : ι → ℝ) (A : ∀ i, Mat (ν i)) :
    tensor (fun i => w i • A i) = (∏ i, w i) • tensor A := by
  ext x y
  simp only [tensor, Matrix.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul,
    Finset.prod_mul_distrib]
  change (∏ i, (w i : ℂ)) * _ = ((∏ i, w i : ℝ) : ℂ) * _
  rw [Complex.ofReal_prod]

lemma tensor_sum_smul {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (w : ∀ i, κ i → ℝ) (A : ∀ i, κ i → Mat (ν i)) :
    tensor (fun i => ∑ k, w i k • A i k) =
      ∑ f : ∀ i, κ i, (∏ i, w i (f i)) • tensor (fun i => A i (f i)) := by
  rw [tensor_sum]
  simp only [tensor_smul]

lemma tensor_mono (A B : ∀ i, Mat (ν i)) (hA : ∀ i, 0 ≤ A i) (hAB : ∀ i, A i ≤ B i) :
    tensor A ≤ tensor B := by
  let M (i : ι) (b : Bool) : Mat (ν i) := if b then B i - A i else A i
  have he (i : ι) : (∑ b : Bool, M i b) = B i := by
    simp [M]
  have hm (i : ι) (b : Bool) : 0 ≤ M i b := by
    cases b
    · exact hA i
    · exact sub_nonneg.mpr (hAB i)
  rw [show B = (fun i => ∑ b : Bool, M i b) by funext i; exact (he i).symm, tensor_sum]
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (ι → Bool)))
    (f := fun f => tensor (fun i => M i (f i)))
    (fun f _ => tensor_nonneg _ (fun i => hm i (f i))) (Finset.mem_univ (fun _ => false))
  exact h
end SpinAngle.DependentTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4107_25 : Fintype τ] [contextInstance4107_37 : DecidableEq τ] [contextInstance4107_53 : Fintype J] [contextInstance4107_65 : DecidableEq J]
  [contextInstance4108_2 : Fintype n] [contextInstance4108_14 : DecidableEq n]
variable (f : τ → J)

lemma tensor_mono (A B : ∀ j, Mat (Fiber f j → n)) (hA : ∀ j, 0 ≤ A j) (hAB : ∀ j, A j ≤ B j) :
    tensor f A ≤ tensor f B := by
  have he := DependentTensor.tensor_mono A B hA hAB
  have hn := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr he)).submatrix (splitEquiv f) |>.nonneg
  exact sub_nonneg.mp hn

lemma tensor_sum_smul {κ : J → Type*} [∀ j, Fintype (κ j)]
    (w : ∀ j, κ j → ℝ) (A : ∀ j, κ j → Mat (Fiber f j → n)) :
    tensor f (fun j => ∑ k, w j k • A j k) =
      ∑ k : ∀ j, κ j, (∏ j, w j (k j)) • tensor f (fun j => A j (k j)) := by
  ext x y
  change DependentTensor.tensor (fun j => ∑ k, w j k • A j k) _ _ = _
  rw [DependentTensor.tensor_sum_smul]
  simp only [Matrix.sum_apply, Matrix.smul_apply, tensor]
end SpinAngle.BlockTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4180_25 : Fintype τ] [contextInstance4180_37 : DecidableEq τ] [contextInstance4180_53 : Fintype J] [contextInstance4180_65 : DecidableEq J]
  [contextInstance4181_2 : Fintype n] [contextInstance4181_14 : DecidableEq n]
variable (f : τ → J)

lemma prod_fibers
    {τ : Type*} {J : Type*}
    [contextInstance4180_25 : Fintype τ]
    [DecidableEq τ]
    [contextInstance4180_53 : Fintype J]
    [contextInstance4180_65 : DecidableEq J]
    (f : τ → J) {M : Type*} [CommMonoid M] (a : τ → M) :
    (∏ j : J, ∏ i : Fiber f j, a i.val) = ∏ i, a i := by
  calc
    _ = ∏ z : Sigma (Fiber f), a z.2.val :=
      (Fintype.prod_sigma (fun z : Sigma (Fiber f) => a z.2.val)).symm
    _ = _ := (Equiv.sigmaFiberEquiv f).prod_comp a

end SpinAngle.BlockTensor

namespace SpinAngle.TensorMatrix
open MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance4214_23 : Fintype ι] [contextInstance4214_35 : DecidableEq ι] [contextInstance4214_51 : Fintype n] [contextInstance4214_63 : DecidableEq n]

end SpinAngle.TensorMatrix

namespace SpinAngle
open scoped BigOperators
variable {R C : Type*} [contextInstance4250_23 : Fintype R] [contextInstance4250_35 : DecidableEq R] [contextInstance4250_51 : Fintype C] [contextInstance4250_63 : DecidableEq C]

end SpinAngle

namespace SpinAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young

namespace TypeLabel
variable {q : ℕ}
lemma projection_isStarProjection (D : TypeLabel q) (τ : Type*) [Fintype τ] [DecidableEq τ] :
    IsStarProjection (D.projection τ) :=
  SignedCarrier.matrixProjection_isStarProjection D.even D.odd q D.even_height D.odd_height

end TypeLabel

namespace EvenDensity
variable {q : ℕ}
variable {J : Type*} [contextInstance4345_21 : Fintype J] [contextInstance4345_33 : Nonempty J]
end EvenDensity

namespace TypeLabel
variable {q : ℕ}
variable {τ : Type*} [contextInstance4358_21 : Fintype τ] [contextInstance4358_33 : DecidableEq τ]
variable [contextInstance4367_9 : Nonempty (Fin q)]
lemma density_mixture (D : TypeLabel q) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (R : ι → EvenDensity q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      D.projection τ ≤ (Real.exp D.entropy * (D.dimension : ℝ)) •
        ∑ i, w i • TensorMatrix.tensor (fun _ : τ => (R i).matrix) := by
  obtain ⟨ι,hι,w,R,hw,hs,hR,hdom⟩ := SignedCarrier.exists_matrix_density_mixture
    (τ := τ) D.even D.odd q D.even_height D.odd_height
  let := hι
  exact ⟨ι,hι,w,fun i => ⟨R i,hR i⟩,hw,hs,hdom⟩
end TypeLabel

namespace TypeBlocks
universe u
open MatrixAnalysis
variable {q : ℕ}
variable {τ : Type*} {J : Type u} [contextInstance4383_34 : Fintype τ] [contextInstance4383_46 : DecidableEq τ] [contextInstance4383_62 : Fintype J] [contextInstance4383_74 : DecidableEq J]

variable [contextInstance4410_9 : Nonempty (Fin q)]

theorem density_mixture (f : τ → J) (D : J → TypeLabel q) :
    ∃ (ι : Type u) (_ : Fintype ι) (w : ι → ℝ) (R : ι → J → EvenDensity q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = Real.exp (entropy D) * (dimension D : ℝ)) ∧
      projection f D ≤ ∑ i, w i • TensorMatrix.tensor (fun t : τ => (R i (f t)).matrix) := by
  classical
  choose κ hκ w R hw hs hdom using (fun j : J => (D j).density_mixture (τ := Fiber f j))
  let : ∀ j, Fintype (κ j) := hκ
  let c (j : J) : ℝ := Real.exp (D j).entropy * (D j).dimension
  let z (j : J) (i : κ j) : ℝ := c j * w j i
  have hz (j : J) (i : κ j) : 0 ≤ z j i :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) (hw j i)
  have hsum (j : J) : ∑ i, z j i = c j := by
    simp only [z, ← Finset.mul_sum, hs, mul_one]
  have hlocal (j : J) : (D j).projection (Fiber f j) ≤
      ∑ i, z j i • TensorMatrix.tensor (fun _ : Fiber f j => (R j i).matrix) := by
    simpa only [z, c, Finset.smul_sum, smul_smul] using hdom j
  refine ⟨(∀ j, κ j), inferInstance, (fun i => ∏ j, z j (i j)),
    (fun i j => R j (i j)), (fun i => Finset.prod_nonneg fun j _ => hz j (i j)), ?_, ?_⟩
  · rw [← Fintype.prod_sum]
    simp only [hsum, c, Finset.prod_mul_distrib]
    rw [← Real.exp_sum]
    simp only [entropy, dimension, Nat.cast_prod]
  · have h := BlockTensor.tensor_mono f _ _
      (fun j => ((D j).projection_isStarProjection (Fiber f j)).nonneg) hlocal
    rw [BlockTensor.tensor_sum_smul] at h
    have he (i : ∀ j, κ j) : BlockTensor.tensor f
        (fun j => TensorMatrix.tensor (fun _ : Fiber f j => (R j (i j)).matrix)) =
        TensorMatrix.tensor (fun t : τ => (R (f t) (i (f t))).matrix) := by
      ext x y
      change (∏ j : J, ∏ t : Fiber f j, (R j (i j)).matrix (x t.val) (y t.val)) =
        ∏ t : τ, (R (f t) (i (f t))).matrix (x t) (y t)
      calc
        _ = ∏ j : J, ∏ t : Fiber f j, (R (f t.val) (i (f t.val))).matrix (x t.val) (y t.val) := by
          apply Finset.prod_congr rfl
          intro j hj
          apply Finset.prod_congr rfl
          intro t ht
          rw [t.property]
        _ = _ := BlockTensor.prod_fibers f (fun t => (R (f t) (i (f t))).matrix (x t) (y t))
    simpa only [he, projection] using h
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

-- ---- platform node ----
open OAI OAI.SpinAngle OAI.SpinAngle.TypeBlocks
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
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young
open MatrixAnalysis


theorem solution.{u,u_1} : type_of% @_root_.OAI.SpinAngle.TypeBlocks.density_mixture.{u,u_1} := @_root_.OAI.SpinAngle.TypeBlocks.density_mixture.{u,u_1}
