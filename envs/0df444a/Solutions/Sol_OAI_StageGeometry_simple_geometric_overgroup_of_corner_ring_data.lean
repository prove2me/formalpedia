-- Prove2me | solution 1 for OAI.StageGeometry.simple_geometric_overgroup_of_corner_ring_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:56:08.176304+00:00
-- url     : https://prove2.me/submissions/ca9b8bd0-4ee5-4b7f-a7f3-9dd6a0977abd

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So030
import Theorems.Thm_OAI_StageGeometry_simple_geometric_overgroup_of_binary_ring_data

section
-- module Solutions.OAIQ066_SO.FiniteType_SourceCorner
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace SourceCorner
variable {R : Type} [Ring R] {e : R} (he : IsIdempotentElem e)

lemma unitEmbedding_injective : Function.Injective (unitEmbedding he) :=
  NonunitalCompression.units_injective (val he) Subtype.val_injective
lemma unitEmbedding_left (u : he.Cornerˣ) (x : he.Corner) :
    (unitEmbedding he u).val*x.val=(u.val*x).val := by
  change (1+(u.val.val-e))*x.val=u.val.val*x.val
  rw [add_mul,sub_mul,one_mul,(Subsemigroup.mem_corner_iff he).mp x.property |>.1]
  abel
lemma unitEmbedding_right (u : he.Cornerˣ) (x : he.Corner) :
    x.val*(unitEmbedding he u).val=(x*u.val).val := by
  change x.val*(1+(u.val.val-e))=x.val*u.val.val
  rw [mul_add,mul_sub,mul_one,(Subsemigroup.mem_corner_iff he).mp x.property |>.2]
  abel
end SourceCorner

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageGeometryProperties
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace StageGeometry
open StageConstruction
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [Group G]
attribute [local instance] OAI.StageGeometry.instDecidableEq_solutions_1
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (he : IsIdempotentElem e) (hne : e≠0)
variable (S T : Y → he.Corner)
variable (hTS : ∀ y y', T y*S y'=if y=y' then 1 else 0)
variable (ρ : W →* he.Cornerˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include φ D hne hTS hρS hTρ hpoint hφ hρ hι hpt F₂ F₃ in
 theorem simple_geometric_overgroup_of_corner_ring_data_oai
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* he.Cornerˣ) (hg : Function.Injective g) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      SimpleFInftyOvergroups.HasTypeFInfty H ∧
        ∃ ν : G →* H, Function.Injective ν := by
  let ρ' := (SourceCorner.unitEmbedding he).comp ρ
  let g' := (SourceCorner.unitEmbedding he).comp g
  let S' : Y → R := fun y => (S y).val
  let T' : Y → R := fun y => (T y).val
  have hρ' : Function.Injective ρ' := (SourceCorner.unitEmbedding_injective he).comp hρ
  have hg' : Function.Injective g' := (SourceCorner.unitEmbedding_injective he).comp hg
  have hTS' : ∀ y y', T' y*S' y'=if y=y' then e else 0 := by
    intro y y'
    change (SourceCorner.val he) (T y)*(SourceCorner.val he) (S y') = _
    rw [← map_mul, hTS]
    split_ifs
    · rfl
    · exact map_zero (SourceCorner.val he)
  have hSe' : ∀ y, S' y*e=S' y := fun y =>
    ((Subsemigroup.mem_corner_iff he).mp (S y).property).2
  have hρS' : ∀ w y, (ρ' w).val*S' y=S' (w • y) := by
    intro w y
    exact (SourceCorner.unitEmbedding_left he (ρ w) (S y)).trans
      (congrArg Subtype.val (hρS w y))
  have hTρ' : ∀ w y, T' y*(ρ' w).val=T' (w⁻¹ • y) := by
    intro w y
    exact (SourceCorner.unitEmbedding_right he (ρ w) (T y)).trans
      (congrArg Subtype.val (hTρ w y))
  exact simple_geometric_overgroup_of_binary_ring_data φ D e S' T' hTS' hSe'
    ρ' ι point hρS' hTρ' hpoint hφ hρ' hι hpt hne F₂ F₃
    A π hπ rel hrel hker g' hg'
end StageGeometry

end
end

end OAI
end

theorem solution : type_of% @OAI.StageGeometry.simple_geometric_overgroup_of_corner_ring_data_oai := @OAI.StageGeometry.simple_geometric_overgroup_of_corner_ring_data_oai
