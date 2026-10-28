-- Prove2me | solution 1 for OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:07:22.39702+00:00
-- url     : https://prove2.me/submissions/0415eba7-9742-48ee-ae02-06d358a15fae

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So016
import Definitions.Def_OAIQ66So034
import Theorems.Thm_OAI_StageGeometry_localGroup_geometric_of_binary_ring_data

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialLimit
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace SequentialLimit

variable {X Y : Type*}

lemma shift_pow_of (s : X → X) (n i : ℕ) (x : X) :
    (shift s ^ n) (of s i x) = of s (i+n) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Equiv.Perm.mul_apply, ih, shift_of, Nat.add_assoc]

lemma stage_mono (s : X → X) {i j : ℕ} (hij : i ≤ j) :
    stage s i ⊆ stage s j := by
  rintro _ ⟨x,rfl⟩
  exact ⟨s^[j-i] x, (of_advance s i j hij x).symm⟩

lemma stage_strict (s : X → X) (hs : Function.Injective s)
    (hn : ¬Function.Surjective s) (i : ℕ) : stage s i ⊂ stage s (i+1) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨stage_mono s (Nat.le_succ i), ?_⟩
  intro h
  apply hn
  intro x
  have hx : of s (i+1) x ∈ stage s i := by
    rw [h]
    exact ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hx
  refine ⟨y, of_injective s hs (i+1) ?_⟩
  simpa only [of_succ] using hy

end SequentialLimit

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PrefixPermutation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace PrefixPermutation
variable {R Y : Type*} [Ring R] [DecidableEq Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)

include hTS in
lemma prefix_injective (he : e≠0) : Function.Injective S := by
  intro y z h
  by_contra hyz
  have eq := congrArg (fun r => T y*r) h
  apply he
  simpa [hTS,hyz] using eq

end PrefixPermutation

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma columnAction_injective : Function.Injective (columnAction (R:=R) (n:=n)) := by
  intro u v h
  apply Units.ext
  ext i j
  have hh := congrArg (fun a : Equiv.Perm (n → R) => a (Pi.single j 1) i) h
  simpa [columnAction,columnPerm,Matrix.mulVec, dotProduct, Pi.single_apply] using hh

end NoncommElementary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.StageConstruction.columnMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace StageConstruction
variable {R : Type*} [Ring R]

lemma action_injective : Function.Injective (action (R:=R)) :=
  NoncommElementary.columnAction_injective.comp Subtype.val_injective

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

lemma beta_injective {Y : Type*} (S : Y → R) (hS : Function.Injective S)
    (hφ : Function.Injective φ) : Function.Injective (beta φ S) := by
  intro y z h
  exact hS (hφ (hφ (by simpa only [beta,Pi.single_eq_same] using congrFun h first)))

lemma beta_not_surjective [Nontrivial R] {Y : Type*} (S : Y → R) :
    ¬Function.Surjective (beta φ S) := by
  intro h
  obtain ⟨y,hy⟩ := h (Pi.single second 1)
  have he := congrFun hy second
  have hne : second≠first := first_ne_second.symm
  simp [beta,hne] at he

variable {Y : Type*} [DecidableEq Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)

variable {W : Type*} [Group W] [MulAction W Y]
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (action q x))

include hTS in
lemma sigma_injective (he : e≠0) (hφ : Function.Injective φ)
    (hpt : Function.Injective point) : Function.Injective (sigma φ S point) :=
  (beta_injective φ S (PrefixPermutation.prefix_injective e S T hTS he) hφ).comp hpt

omit [DecidableEq Y] in
lemma sigma_not_surjective [Nontrivial R] : ¬Function.Surjective (sigma φ S point) := by
  intro h
  apply beta_not_surjective φ S
  intro y
  obtain ⟨x,hx⟩ := h y
  exact ⟨point x,hx⟩

end StageConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace TorusAction
open SequentialLimit SequentialAction AscendingHNN
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

lemma basePerm_stage (g : U) (i : ℕ) :
    basePerm f s heq g '' stage s i = stage s i := by
  ext x
  constructor
  · rintro ⟨_,⟨y,rfl⟩,rfl⟩
    exact ⟨(f : U → U)^[i] g • y,(basePerm_of f s heq g i y).symm⟩
  · rintro ⟨y,rfl⟩
    refine ⟨of s i (((f : U → U)^[i] g)⁻¹ • y),⟨_,rfl⟩,?_⟩
    rw [basePerm_of,smul_inv_smul]

lemma shift_pow_stage (i n : ℕ) : ((shift s)^n) '' stage s i = stage s (i+n) := by
  ext x
  constructor
  · rintro ⟨_,⟨y,rfl⟩,rfl⟩
    exact ⟨y,(shift_pow_of s n i y).symm⟩
  · rintro ⟨y,rfl⟩
    exact ⟨of s i y,⟨y,rfl⟩,shift_pow_of s n i y⟩

lemma representation_injective [FaithfulSMul U X] (hs : Function.Injective s)
    (hn : ¬ Function.Surjective s) : Function.Injective (representation f hf s heq) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨a,b,u,rfl⟩ := normal_form f hf g
  simp only [map_mul,map_pow,map_inv,representation_stable,representation_embed] at hg
  have he : (shift s)^a * basePerm f s heq u = (shift s)^b := by
    apply mul_right_cancel (b := ((shift s)^b)⁻¹)
    rw [hg,mul_inv_cancel]
  have hst : stage s a = stage s b := by
    have hh := congrArg (fun e : Equiv.Perm (Limit s) => e '' stage s 0) he
    change (fun x => ((shift s)^a) (basePerm f s heq u x)) '' stage s 0 =
      ((shift s)^b) '' stage s 0 at hh
    rw [← Set.image_image,basePerm_stage,shift_pow_stage,shift_pow_stage] at hh
    simpa only [Nat.zero_add] using hh
  have hab : a=b := (strictMono_nat_of_lt_succ (stage_strict s hs hn)).injective hst
  subst b
  have hu : basePerm f s heq u = 1 := by
    apply mul_left_cancel (a := (shift s)^a)
    simpa only [mul_one] using he
  have hu' : u=1 := by
    apply eq_of_smul_eq_smul (α := X)
    intro x
    apply of_injective s hs 0
    have hux := congrArg (fun e : Equiv.Perm (Limit s) => e (of s 0 x)) hu
    simpa only [basePerm_of,Function.iterate_zero,id_eq,Equiv.Perm.one_apply,one_smul] using hux
  simp [hu']

end TorusAction

namespace StageConstruction
variable {R : Type*} [Ring R]

instance columnFaithful : FaithfulSMul (Q R) (X R) where
  eq_of_smul_eq_smul h := action_injective (Equiv.ext h)

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable {Y W : Type*} [DecidableEq Y] [Group W] [MulAction W Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point)

include hTS hpt in
                                                                                  
lemma limitRepresentation_injective [Nontrivial R] (he : e≠0) :
    Function.Injective (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) := by
  exact @TorusAction.representation_injective (Q R) (X R) _ columnMulAction
    (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
    (sigma φ S point) (fun q x => (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm)
    columnFaithful (sigma_injective φ e S T hTS point he hφ hpt)
    (sigma_not_surjective φ S point)

include φ point hφ hpt hTS in
lemma stagePoints_infinite [Nontrivial R] (he : e≠0) : Infinite (X R) := by
  apply not_finite_iff_infinite.mp
  intro h
  let : Finite (X R) := h
  exact sigma_not_surjective φ S point
    (Finite.injective_iff_surjective.mp (sigma_injective φ e S T hTS point he hφ hpt))

include hφ hpt hTS in
lemma limitPoints_infinite [Nontrivial R] (he : e≠0) : Infinite (LimitPoints φ S point) := by
  let := stagePoints_infinite φ e S T hTS point hφ hpt he
  exact Infinite.of_injective (SequentialLimit.of (sigma φ S point) 0)
    (SequentialLimit.of_injective (sigma φ S point) (sigma_injective φ e S T hTS point he hφ hpt) 0)

end StageConstruction

end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.LocalEmbedding.instCoeFunForallBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin

lemma continuous_get (n : ℕ) : Continuous (fun x : Cantor => x.get n) := continuous_apply n

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma isOpen_brick (p : Prefix S) : IsOpen p.brick := by
  classical
  let : Finite {s : S // p s ≠ []} := p.finite_support.to_subtype
  let I := (s : {s : S // p s ≠ []}) × Fin (p s.1).length
  have he : p.brick = ⋂ j : I, {x | (x j.1.1).get j.2 = (p j.1.1)[j.2]} := by
    ext x
    simp only [mem_brick_iff_get,mem_iInter,mem_ofPred_eq]
    constructor
    · intro h j; exact h j.1.1 j.2 j.2.isLt
    · intro h s n hn
      have hs : p s ≠ [] := by intro he; simp [he] at hn
      exact h ⟨⟨s,hs⟩,⟨n,hn⟩⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_discrete {(p j.1.1)[j.2]}).preimage
    ((continuous_get (j.2.val)).comp (continuous_apply j.1.1))

end TwistedBrin.Prefix

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma finite_local_cover {f : Equiv.Perm (Box S)} (hf : IsLocal ρ f) :
    ∃ (I : Finset (Box S)) (p q : Box S → Prefix S) (a : Box S → A),
      (∀ i y, f ((p i).chart y) = (q i).chart (twist ρ (a i) y)) ∧
      ∀ x, ∃ i ∈ I, x ∈ (p i).brick := by
  classical
  choose p q a hp he using hf
  have hcover : (Set.univ : Set (Box S)) ⊆ ⋃ i, (p i).brick := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hp x⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (p i).brick) (fun i => (p i).isOpen_brick) hcover
  refine ⟨I,p,q,a,he,?_⟩
  intro x
  simpa only [Set.mem_iUnion,exists_prop] using hI (Set.mem_univ x)

lemma finite_grid_refinement (I : Finset (Box S)) (p : Box S → Prefix S)
    (hc : ∀ x, ∃ i ∈ I, x ∈ (p i).brick) :
    ∃ b : S →₀ ℕ, ∀ z : Prefix.Grid b, ∃ i ∈ I,
      Prefix.Extends (p i) (Prefix.gridPrefix b z) := by
  classical
  let b : S →₀ ℕ := ∑ i ∈ I, (p i).lengths
  refine ⟨b,?_⟩
  intro z
  let x : Box S := (Prefix.gridPrefix b z).chart (fun _ _ => false)
  obtain ⟨i,hi,hix⟩ := hc x
  refine ⟨i,hi,Prefix.extends_of_mem_of_length_le hix (Prefix.chart_mem_brick _ _) ?_⟩
  intro s
  rw [Prefix.gridPrefix_length]
  change (p i).lengths s ≤ b s
  have hl : (p i).lengths ≤ ∑ j ∈ I, (p j).lengths :=
    Finset.single_le_sum (f := fun j => (p j).lengths) (fun _ _ s => Nat.zero_le _) hi
  exact hl s

lemma hasTable_of_isLocal {f : Equiv.Perm (Box S)} (hf : IsLocal ρ f) : HasTable ρ f := by
  classical
  obtain ⟨I,p,q,a,he,hc⟩ := finite_local_cover ρ hf
  obtain ⟨b,hb⟩ := finite_grid_refinement I p hc
  choose i hi hr using hb
  let r : Prefix.Grid b → Prefix S := Prefix.gridPrefix b
  let t : Prefix.Grid b → Prefix S := fun z =>
    Prefix.append (q (i z)) ((Prefix.suffix (p (i z)) (r z)).permute (ρ (a (i z))))
  have hchart (z : Prefix.Grid b) (y : Box S) :
      f ((r z).chart y) = (t z).chart (twist ρ (a (i z)) y) := by
    change f ((Prefix.gridPrefix b z).chart y) = _
    nth_rw 1 [← Prefix.append_suffix (hr z)]
    rw [Prefix.chart_append,he,twist_chart,← Prefix.chart_append]
  have ht : IsPartition t := by
    intro x
    obtain ⟨z,hz,hzu⟩ := Prefix.grid_partition b (f.symm x)
    have hmem : x ∈ (t z).brick := by
      obtain ⟨y,hy⟩ := hz
      refine ⟨twist ρ (a (i z)) y,?_⟩
      rw [← hchart,hy,f.apply_symm_apply]
    refine ⟨z,hmem,?_⟩
    intro w hw
    apply hzu w
    obtain ⟨y,hy⟩ := hw
    refine ⟨twist ρ (a (i w))⁻¹ y,?_⟩
    apply f.injective
    rw [hchart,← twist_mul,mul_inv_cancel,twist_one,hy,f.apply_symm_apply]
  let e := Fintype.equivFin (Prefix.Grid b)
  let T : Table (A := A) (S := S) := {
    size := Fintype.card (Prefix.Grid b)
    dom := fun j => r (e.symm j)
    ran := fun j => t (e.symm j)
    label := fun j => a (i (e.symm j))
    dom_partition := by
      intro x
      obtain ⟨z,hz,hu⟩ := Prefix.grid_partition b x
      refine ⟨e z,by simpa using hz,?_⟩
      intro j hj
      exact (e.symm_apply_eq).mp (hu _ hj)
    ran_partition := by
      intro x
      obtain ⟨z,hz,hu⟩ := ht x
      refine ⟨e z,by simpa using hz,?_⟩
      intro j hj
      exact (e.symm_apply_eq).mp (hu _ hj) }
  exact ⟨T,fun j y => hchart (e.symm j) y⟩

end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactSubtypeOfExactSet
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)

lemma globalHom_injective (hρ : Function.Injective ρ) : Function.Injective (globalHom ρ) := by
  intro a b he
  exact twist_injective ρ hρ (congrArg Subtype.val he)

end TwistedBrin

namespace StageGeometry
open StageConstruction
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [DecidableEq Y] [Group G]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y y', T y*S y'=if y=y' then e else 0) (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point) (he : e≠0)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include hTS hSe hTρ hpt he F₂ F₃ in

theorem localGroup_overgroup_of_binary_ring_data
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* Rˣ) (hg : Function.Injective g) :
    SimpleFInftyOvergroups.HasTypeFInfty
      (TwistedBrin.localGroup (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι)) ∧
    ∃ ν : G →* TwistedBrin.localGroup (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι),
      Function.Injective ν := by
  refine ⟨localGroup_geometric_of_binary_ring_data φ D e S T hTS hSe ρ ι point
    hρS hTρ hpoint hφ hρ hι hpt he F₂ F₃ A π hπ rel hrel hker,?_⟩
  let σ := limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι
  let j := (AscendingHNN.embed (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)).comp
    ((transitionUnits φ D).comp g)
  refine ⟨(TwistedBrin.globalHom σ).comp j,?_⟩
  apply (TwistedBrin.globalHom_injective σ
    (limitRepresentation_injective φ D e S T hTS ρ ι point hρS hpoint hφ hρ hι hpt he)).comp
  exact (AscendingHNN.embed_injective _ _).comp ((transitionUnits_injective φ D hφ).comp hg)
end StageGeometry

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinEquiv
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped commutatorElement
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix

lemma grid_of_chart (p : Prefix S) (x : Box S) :
    gridPrefix p.lengths (gridPoint p.lengths (p.chart x)) = p := by
  apply Prefix.ext
  intro s
  apply List.ext_getElem
  · simp [gridPrefix_length]
  · intro n hn hm
    have hz := (mem_brick_iff_get _ _).mp (mem_gridPrefix p.lengths (p.chart x)) s n hn
    have hp := (mem_brick_iff_get p _).mp (chart_mem_brick p x) s n hm
    exact hz.symm.trans hp

end Prefix
namespace Localization

lemma gridIndex_prefix (p : Prefix S) : Prefix.gridPrefix p.lengths (gridIndex p) = p :=
  Prefix.grid_of_chart p _

lemma chart (p : Prefix S) (g : localGroup ρ) (x : Box S) :
    (hom ρ p g).val (p.chart x) = p.chart (g.val x) := by
  classical
  conv_lhs => arg 2; rw [← gridIndex_prefix p]
  change (PartitionMaps.pieces ρ _ _ (Pi.mulSingle (gridIndex p) g)).val _ = _
  rw [PartitionMaps.pieces_chart,Pi.mulSingle_eq_same,gridIndex_prefix]

lemma outside (p : Prefix S) (g : localGroup ρ) (x : Box S) (hx : x ∉ p.brick) :
    (hom ρ p g).val x = x := by
  classical
  obtain ⟨i,⟨y,hy⟩,_⟩ := Prefix.grid_partition p.lengths x
  have hi : i ≠ gridIndex p := by
    intro hi
    subst i
    rw [gridIndex_prefix] at hy
    exact hx ⟨y,hy⟩
  rw [← hy]
  change (PartitionMaps.pieces ρ _ _ (Pi.mulSingle (gridIndex p) g)).val _ = _
  rw [PartitionMaps.pieces_chart,Pi.mulSingle_eq_of_ne hi]
  rfl

end Localization
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Localization

lemma conjugate (p q : Prefix S) (h g : localGroup ρ)
    (he : ∀ x, h.val (p.chart x)=q.chart x) :
    h * hom ρ p g * h⁻¹ = hom ρ q g := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩ := h.val.surjective x
  change h.val ((hom ρ p g).val (h.val.symm (h.val y))) = _
  rw [h.val.symm_apply_apply]
  by_cases hp : y ∈ p.brick
  · obtain ⟨z,rfl⟩ := hp
    rw [chart,he,he,chart]
  · have hq : h.val y ∉ q.brick := by
      rintro ⟨z,hz⟩
      exact hp ⟨z,h.val.injective ((he z).trans hz)⟩
    rw [outside ρ p g y hp,outside ρ q g _ hq]

lemma conjugate_swap (p q : Prefix S) (hd : Disjoint p.brick q.brick) (g : localGroup ρ) :
    BrickSwap.elem ρ p q hd * hom ρ p g * (BrickSwap.elem ρ p q hd)⁻¹ = hom ρ q g :=
  conjugate ρ p q _ g (BrickSwap.elem_left ρ p q hd)

lemma append (p q : Prefix S) (g : localGroup ρ) :
    hom ρ (p.append q) g = hom ρ p (hom ρ q g) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hx
    rw [chart]
    by_cases hy : y ∈ q.brick
    · obtain ⟨z,rfl⟩ := hy
      rw [← Prefix.chart_append,chart,Prefix.chart_append,chart]
    · have hxy : p.chart y ∉ (p.append q).brick := by
        rintro ⟨z,hz⟩
        rw [Prefix.chart_append] at hz
        exact hy ⟨z,p.chart_injective hz⟩
      rw [outside ρ (p.append q) g _ hxy,outside ρ q g _ hy]
  · have hxy : x ∉ (p.append q).brick := fun hh => hx (Prefix.brick_append_subset p q hh)
    rw [outside ρ (p.append q) g x hxy,outside ρ p _ x hx]

end Localization
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix
lemma exists_disjoint {p : Prefix S} (hp : p ≠ empty) :
    ∃ q : Prefix S, Disjoint p.brick q.brick := by
  classical
  have hn : p.brick ≠ Set.univ := fun h => hp (eq_empty_of_brick_univ h)
  obtain ⟨x,hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hn
  exact ⟨gridPrefix p.lengths (gridPoint p.lengths x),
    disjoint_of_length (mem_gridPrefix p.lengths x) hx (by intro s; rw [gridPrefix_length]; exact le_rfl)⟩

lemma cut_ne_empty (s : S) (b : Bool) : cut s b ≠ empty := by
  intro h
  have := congrArg (fun p : Prefix S => p s) h
  simp at this

lemma append_ne_empty_left {p : Prefix S} (hp : p ≠ empty) (q : Prefix S) :
    p.append q ≠ empty := by
  intro h
  apply hp
  apply Prefix.ext
  intro s
  have hh := congrArg (fun p : Prefix S => p s) h
  exact (List.append_eq_nil_iff.mp hh).1

lemma chart_cut_commute (p : Prefix S) (s : S) (hp : p s = []) (b : Bool) (x : Box S) :
    p.chart ((cut s b).chart x) = (cut s b).chart (p.chart x) := by
  classical
  rw [← chart_append,← chart_append]
  congr 1
  apply Prefix.ext
  intro t
  by_cases ht : t=s
  · subst t; simp [append_apply,hp]
  · simp [append_apply,cut_apply,ht]

lemma mem_cut_chart_iff (p : Prefix S) (s : S) (hp : p s=[]) (b : Bool) (x : Box S) :
    (cut s b).chart x ∈ p.brick ↔ x ∈ p.brick := by
  rw [mem_brick_iff_get,mem_brick_iff_get]
  constructor <;> intro h t n hn
  · by_cases ht : t=s
    · subst t; simp [hp] at hn
    · simpa [chart,cut_apply,ht] using h t n hn
  · by_cases ht : t=s
    · subst t; simp [hp] at hn
    · simpa [chart,cut_apply,ht] using h t n hn
end Prefix
namespace Localization
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)

lemma image_eq_of_disjoint (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
    {p q : Prefix S} (hd : Disjoint p.brick q.brick) (g : localGroup ρ) :
    π (hom ρ p g)=π (hom ρ q g) := by
  have h := congrArg π (conjugate_swap ρ p q hd g)
  rw [map_mul,map_mul,map_inv] at h
  rw [(hc p q hd (hom ρ p g)).eq, mul_assoc,mul_inv_cancel,mul_one] at h
  exact h

lemma image_eq_proper (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
    {p q : Prefix S} (hp : p ≠ Prefix.empty) (hq : q ≠ Prefix.empty) (g : localGroup ρ) :
    π (hom ρ p g)=π (hom ρ q g) := by
  classical
  obtain ⟨r,hpr⟩ := Prefix.exists_disjoint hp
  obtain ⟨u,hqu⟩ := Prefix.exists_disjoint hq
  by_cases hrq : Disjoint r.brick q.brick
  · exact (image_eq_of_disjoint ρ π hc hpr g).trans (image_eq_of_disjoint ρ π hc hrq g)
  · obtain ⟨x,hxr,hxq⟩ := Set.not_disjoint_iff.mp hrq
    let v := Prefix.common x r q
    have hvr : v.brick ⊆ r.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_left hxr)
    have hvq : v.brick ⊆ q.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_right hxq)
    exact (image_eq_of_disjoint ρ π hc (hpr.mono_right hvr) g).trans
      ((image_eq_of_disjoint ρ π hc (hqu.mono_left hvq) g).trans
        (image_eq_of_disjoint ρ π hc hqu.symm g))
end Localization

namespace Stationary
lemma split {s : S} {g : localGroup ρ} (hg : Stationary ρ s g) :
    g = Localization.hom ρ (Prefix.cut s false) g * Localization.hom ρ (Prefix.cut s true) g := by
  apply PartitionMaps.ext ρ (Prefix.cut s) (Prefix.cut_partition s)
  intro b x
  change g.val _ = (Localization.hom ρ _ g).val ((Localization.hom ρ _ g).val _)
  cases b
  · have hn : (Prefix.cut s false).chart x ∉ (Prefix.cut s true).brick := by
      intro hh
      exact Bool.false_ne_true (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ x) hh))
    rw [Localization.outside ρ _ g _ hn,Localization.chart,hg]
  · rw [Localization.chart]
    have hn : (Prefix.cut s true).chart (g.val x) ∉ (Prefix.cut s false).brick := by
      intro hh
      exact Bool.noConfusion (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ (g.val x)) hh))
    rw [Localization.outside ρ _ g _ hn,hg]

lemma localize {s : S} {g : localGroup ρ} (hg : Stationary ρ s g)
    (p : Prefix S) (hp : p s=[]) : Stationary ρ s (Localization.hom ρ p g) := by
  intro b x
  by_cases hx : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hx
    rw [← Prefix.chart_cut_commute p s hp,Localization.chart,hg,
      Prefix.chart_cut_commute p s hp,Localization.chart]
  · rw [Localization.outside ρ p g x hx,
      Localization.outside ρ p g _ (fun h => hx ((Prefix.mem_cut_chart_iff p s hp b x).mp h))]
end Stationary
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Stationary
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc

lemma local_image_eq_one {s : S} {g : localGroup ρ} (hg : Stationary ρ s g)
    {p : Prefix S} (hp : p ≠ Prefix.empty) : π (Localization.hom ρ p g)=1 := by
  have hh := congrArg (fun k => π (Localization.hom ρ p k)) (split ρ hg)
  rw [map_mul,map_mul,← Localization.append,← Localization.append] at hh
  rw [Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp,
    Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp] at hh
  exact (mul_eq_left.mp hh.symm)

lemma image_eq_one {s : S} {g : localGroup ρ} (hg : Stationary ρ s g) : π g=1 := by
  rw [split ρ hg,map_mul,local_image_eq_one ρ π hc hg (Prefix.cut_ne_empty _ _),
    local_image_eq_one ρ π hc hg (Prefix.cut_ne_empty _ _),one_mul]
end Stationary
namespace PartitionMaps
variable {I : Type} [Fintype I]
lemma stationary_rearrange (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q)
    {s : S} (hs : ∀ i, p i s=[] ∧ q i s=[]) :
    Stationary ρ s (rearrange ρ p q hp hq) := by
  intro b x
  obtain ⟨i,⟨y,rfl⟩,_⟩ := hp x
  rw [← Prefix.chart_cut_commute (p i) s (hs i).1,
    rearrange_chart,rearrange_chart,Prefix.chart_cut_commute (q i) s (hs i).2]

lemma fresh [Infinite S] (p q : I → Prefix S) (r : Prefix S) :
    ∃ s : S, r s=[] ∧ ∀ i, p i s=[] ∧ q i s=[] := by
  classical
  have hf := ((Set.finite_iUnion fun i => (p i).finite_support).union
    (Set.finite_iUnion fun i => (q i).finite_support)).union r.finite_support
  obtain ⟨s,hs⟩ := hf.exists_notMem
  simp only [Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,not_or,not_exists,not_not] at hs
  exact ⟨s,hs.2,fun i => ⟨hs.1.1 i,hs.1.2 i⟩⟩

variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc

lemma rearrange_image [Infinite S] (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q) :
    π (rearrange ρ p q hp hq)=1 := by
  obtain ⟨s,_,hs⟩ := fresh p q Prefix.empty
  exact Stationary.image_eq_one ρ π hc (stationary_rearrange ρ p q hp hq hs)

lemma rearrange_local_image [Infinite S] (p q : I → Prefix S) (hp : IsPartition p)
    (hq : IsPartition q) (r : Prefix S) : π (Localization.hom ρ r (rearrange ρ p q hp hq))=1 := by
  obtain ⟨s,hr,hs⟩ := fresh p q r
  exact Stationary.image_eq_one ρ π hc
    (Stationary.localize ρ (stationary_rearrange ρ p q hp hq hs) r hr)
end PartitionMaps
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Localization
lemma cuts_chart (s : S) (g : localGroup ρ) (b : Bool) (x : Box S) :
    (hom ρ (Prefix.cut s false) g * hom ρ (Prefix.cut s true) g).val
      ((Prefix.cut s b).chart x) = (Prefix.cut s b).chart (g.val x) := by
  change (hom ρ _ g).val ((hom ρ _ g).val _) = _
  cases b
  · have hn : (Prefix.cut s false).chart x ∉ (Prefix.cut s true).brick := by
      intro hh
      exact Bool.false_ne_true (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ x) hh))
    rw [outside ρ _ g _ hn,chart]
  · rw [chart]
    have hn : (Prefix.cut s true).chart (g.val x) ∉ (Prefix.cut s false).brick := by
      intro hh
      exact Bool.noConfusion (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ (g.val x)) hh))
    rw [outside ρ _ g _ hn]

@[simp] lemma empty (g : localGroup ρ) : hom ρ Prefix.empty g=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact chart ρ Prefix.empty g x
end Localization

lemma global_split (a : A) (s : S) :
    globalHom ρ a =
      PartitionMaps.rearrange ρ (Prefix.cut s) (Prefix.cut (ρ a s))
        (Prefix.cut_partition s) (Prefix.cut_partition (ρ a s)) *
      (Localization.hom ρ (Prefix.cut s false) (globalHom ρ a) *
        Localization.hom ρ (Prefix.cut s true) (globalHom ρ a)) := by
  apply PartitionMaps.ext ρ (Prefix.cut s) (Prefix.cut_partition s)
  intro b x
  change twist ρ a _ = _
  rw [twist_chart,Prefix.permute_cut]
  simp only [Subgroup.coe_mul,Equiv.Perm.mul_apply]
  rw [show (Localization.hom ρ (Prefix.cut s false) (globalHom ρ a)).val
      ((Localization.hom ρ (Prefix.cut s true) (globalHom ρ a)).val ((Prefix.cut s b).chart x)) =
      (Prefix.cut s b).chart ((globalHom ρ a).val x) from Localization.cuts_chart ρ s _ b x,
    PartitionMaps.rearrange_chart]
  rfl

namespace PerfectProducer
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc
lemma global_local_image [Infinite S] (a : A) {p : Prefix S} (hp : p ≠ Prefix.empty) :
    π (Localization.hom ρ p (globalHom ρ a))=1 := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  have hh := congrArg (fun g => π (Localization.hom ρ p g)) (global_split ρ a s)
  rw [map_mul,map_mul,map_mul,map_mul,PartitionMaps.rearrange_local_image ρ π hc,
    one_mul,← Localization.append,← Localization.append] at hh
  rw [Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp,
    Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp] at hh
  exact mul_eq_left.mp hh.symm

lemma global_image [Infinite S] (a : A) : π (globalHom ρ a)=1 := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  rw [global_split ρ a s,map_mul,map_mul,PartitionMaps.rearrange_image ρ π hc,
    global_local_image ρ π hc a (Prefix.cut_ne_empty _ _),
    global_local_image ρ π hc a (Prefix.cut_ne_empty _ _),one_mul,one_mul]

lemma global_local_image_all [Infinite S] (a : A) (p : Prefix S) :
    π (Localization.hom ρ p (globalHom ρ a))=1 := by
  by_cases hp : p=Prefix.empty
  · subst p; rw [Localization.empty]; exact global_image ρ π hc a
  · exact global_local_image ρ π hc a hp
end PerfectProducer
namespace PartitionMaps
variable {I : Type} [Fintype I]
lemma pieces_mulSingle [DecidableEq I] (p : I → Prefix S) (hp : IsPartition p)
    (i : I) (g : localGroup ρ) :
    pieces ρ p hp (Pi.mulSingle i g) = Localization.hom ρ (p i) g := by
  apply ext ρ p hp
  intro j x
  rw [pieces_chart]
  by_cases hj : j=i
  · subst j; rw [Pi.mulSingle_eq_same,Localization.chart]
  · rw [Pi.mulSingle_eq_of_ne hj]
    have hn : (p j).chart x ∉ (p i).brick := fun hh =>
      hj ((hp _).unique (Prefix.chart_mem_brick _ _) hh)
    rw [Localization.outside ρ _ g _ hn]
    rfl
end PartitionMaps
namespace PerfectProducer
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc
lemma pieces_global_image [Infinite S] {I : Type} [Fintype I]
    (p : I → Prefix S) (hp : IsPartition p) (a : I → A) :
    π (PartitionMaps.pieces ρ p hp (fun i => globalHom ρ (a i)))=1 := by
  classical
  let f : (I → A) →* Q :=
    (π.comp (PartitionMaps.piecesHom ρ p hp)).comp (MonoidHom.piMap fun _ : I => globalHom ρ)
  have hf : f=1 := by
    apply MonoidHom.pi_ext
    intro i b
    simp only [f,MonoidHom.comp_apply,MonoidHom.one_apply,PartitionMaps.piecesHom_apply]
    change π (PartitionMaps.pieces ρ p hp (fun j : I => globalHom ρ ((Pi.mulSingle i b : I → A) j))) = 1
    have he : (fun j : I => globalHom ρ ((Pi.mulSingle i b : I → A) j))=(Pi.mulSingle i (globalHom ρ b) : I → localGroup ρ) := by
      funext j
      by_cases hj : j=i
      · subst j; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [he,PartitionMaps.pieces_mulSingle,global_local_image_all ρ π hc]
  exact DFunLike.congr_fun hf a

lemma hom_eq_one [Infinite S] (g : localGroup ρ) : π g=1 := by
  obtain ⟨T,hT⟩ := hasTable_of_isLocal ρ g.property
  have he : g = PartitionMaps.rearrange ρ T.dom T.ran T.dom_partition T.ran_partition *
      PartitionMaps.pieces ρ T.dom T.dom_partition (fun i => globalHom ρ (T.label i)) := by
    apply PartitionMaps.ext ρ T.dom T.dom_partition
    intro i x
    change g.val ((T.dom i).chart x) =
      (PartitionMaps.rearrange ρ T.dom T.ran T.dom_partition T.ran_partition).val
      ((PartitionMaps.pieces ρ T.dom T.dom_partition (fun i => globalHom ρ (T.label i))).val
        ((T.dom i).chart x))
    rw [PartitionMaps.pieces_chart,PartitionMaps.rearrange_chart]
    exact hT i x
  rw [he,map_mul,PartitionMaps.rearrange_image ρ π hc,pieces_global_image ρ π hc,one_mul]

end PerfectProducer
lemma localGroup_perfect [Infinite S] : Group.IsPerfect (localGroup ρ) := by
  constructor
  rw [← Abelianization.ker_of]
  apply top_unique
  intro g _
  exact PerfectProducer.hom_eq_one ρ Abelianization.of (fun _ _ _ _ => Commute.all _ _) g
end TwistedBrin

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinSeparated
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped commutatorElement
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix
lemma separated {x y : Box S} (hxy : x ≠ y) :
    ∃ p q : Prefix S, x ∈ p.brick ∧ y ∈ q.brick ∧ Disjoint p.brick q.brick := by
  classical
  have hh : ∃ s n, (x s).get n ≠ (y s).get n := by
    contrapose! hxy
    funext s n
    exact hxy s n
  obtain ⟨s,n,hn⟩ := hh
  let b := Finsupp.single s (n+1)
  let p := gridPrefix b (gridPoint b x)
  let q := gridPrefix b (gridPoint b y)
  have hp := mem_gridPrefix b x
  have hq := mem_gridPrefix b y
  refine ⟨p,q,hp,hq,Set.disjoint_left.mpr ?_⟩
  intro z hz hzq
  have hnp : n < (p s).length := by simp [p,gridPrefix_length,b]
  have hnq : n < (q s).length := by simp [q,gridPrefix_length,b]
  exact hn (((mem_brick_iff_get p x).mp hp s n hnp).trans
    (((mem_brick_iff_get p z).mp hz s n hnp).symm.trans
      (((mem_brick_iff_get q z).mp hzq s n hnq).trans
        ((mem_brick_iff_get q y).mp hq s n hnq).symm)))
end Prefix

lemma exists_displaced_brick {g : localGroup ρ} (hg : g ≠ 1) :
    ∃ (p q : Prefix S) (a : A), Disjoint p.brick q.brick ∧
      ∀ y, g.val (p.chart y)=q.chart (twist ρ a y) := by
  classical
  have hx : ∃ x : Box S, g.val x ≠ x := by
    by_contra hh
    push Not at hh
    apply hg
    apply Subtype.ext
    exact Equiv.ext hh
  obtain ⟨x,hx⟩ := hx
  obtain ⟨R,T,hxR,hxT,hRT⟩ := Prefix.separated hx.symm
  obtain ⟨u,v,a,hxu,he⟩ := g.property x
  let p := Prefix.common x u R
  let c := u.suffix p
  let q := v.append (c.permute (ρ a))
  have huc : u.append c=p := Prefix.append_suffix (Prefix.extends_common_left hxu)
  have hp : x ∈ p.brick := Prefix.mem_common _ _ _
  have hep (y : Box S) : g.val (p.chart y)=q.chart (twist ρ a y) := by
    rw [← huc,Prefix.chart_append,he,twist_chart,← Prefix.chart_append]
  have hq : g.val x ∈ q.brick := by
    obtain ⟨y,hy⟩ := hp
    exact ⟨twist ρ a y,by rw [← hep,hy]⟩
  let z := Prefix.common (g.val x) q T
  let d := q.suffix z
  let P := p.append (d.permute (ρ a⁻¹))
  have hqd : q.append d=z := Prefix.append_suffix (Prefix.extends_common_left hq)
  have heP (y : Box S) : g.val (P.chart y)=z.chart (twist ρ a y) := by
    change g.val ((p.append (d.permute (ρ a⁻¹))).chart y)=_
    rw [Prefix.chart_append,hep,twist_chart,twist_prefix_inv,← Prefix.chart_append,hqd]
  refine ⟨P,z,a,hRT.mono ?_ ?_,heP⟩
  · exact (Prefix.brick_append_subset p _).trans
      (Prefix.brick_subset_of_extends (Prefix.extends_common_right hxR))
  · exact Prefix.brick_subset_of_extends (Prefix.extends_common_right hxT)

namespace Localization
lemma commute_of_disjoint_support {U V : Set (Box S)} (hd : Disjoint U V)
    (g h : localGroup ρ) (hg : ∀ x, x ∉ U → g.val x=x) (hh : ∀ x, x ∉ V → h.val x=x) :
    Commute g h := by
  have hgm : ∀ x ∈ U, g.val x ∈ U := by
    intro x hx
    by_contra hn
    have he : g.val x=x := g.val.injective (hg (g.val x) hn)
    exact hn (he.symm ▸ hx)
  have hhm : ∀ x ∈ V, h.val x ∈ V := by
    intro x hx
    by_contra hn
    have he : h.val x=x := h.val.injective (hh (h.val x) hn)
    exact hn (he.symm ▸ hx)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change g.val (h.val x)=h.val (g.val x)
  by_cases hx : x ∈ U
  · rw [hh x (fun h => Set.disjoint_left.mp hd hx h),
      hh (g.val x) (fun h => Set.disjoint_left.mp hd (hgm x hx) h)]
  · by_cases hv : x ∈ V
    · rw [hg x hx,hg (h.val x) (fun h => Set.disjoint_left.mp hd h (hhm x hv))]
    · rw [hg x hx,hh x hv,hg x hx]

lemma conjugate_outside {p q : Prefix S} {a : A} {f : localGroup ρ}
    (hf : ∀ y, f.val (p.chart y)=q.chart (twist ρ a y)) (g : localGroup ρ)
    (x : Box S) (hx : x ∉ q.brick) : (f * hom ρ p g * f⁻¹).val x=x := by
  have hy : f.val.symm x ∉ p.brick := by
    rintro ⟨y,hy⟩
    apply hx
    refine ⟨twist ρ a y,?_⟩
    rw [← hf,hy,f.val.apply_symm_apply]
  change f.val ((hom ρ p g).val (f.val.symm x))=x
  rw [outside ρ p g _ hy,f.val.apply_symm_apply]
end Localization
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace BrickSwap
lemma stationary {p q : Prefix S} (hd : Disjoint p.brick q.brick) {s : S}
    (hp : p s=[]) (hq : q s=[]) : Stationary ρ s (elem ρ p q hd) := by
  intro b x
  by_cases hx : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hx
    rw [← Prefix.chart_cut_commute p s hp,elem_left,elem_left,Prefix.chart_cut_commute q s hq]
  · by_cases hxq : x ∈ q.brick
    · obtain ⟨y,rfl⟩ := hxq
      rw [← Prefix.chart_cut_commute q s hq,elem_right,elem_right,Prefix.chart_cut_commute p s hp]
    · change fn p q ((Prefix.cut s b).chart x) = (Prefix.cut s b).chart (fn p q x)
      rw [outside p q x hx hxq,outside p q _
        (fun hh => hx ((Prefix.mem_cut_chart_iff p s hp b x).mp hh))
        (fun hh => hxq ((Prefix.mem_cut_chart_iff q s hq b x).mp hh))]
end BrickSwap
namespace SimplicityProducer
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)

lemma kills_disjoint {p q : Prefix S} (hd : Disjoint p.brick q.brick)
    (hp : KillsBrick ρ π p) : KillsBrick ρ π q := by
  intro g
  have h := congrArg π (Localization.conjugate_swap ρ p q hd g)
  rw [map_mul,map_mul,map_inv,hp g,mul_one,mul_inv_cancel] at h
  exact h.symm

lemma kills_proper {p : Prefix S} (hp : p ≠ Prefix.empty) (hk : KillsBrick ρ π p)
    {q : Prefix S} (hq : q ≠ Prefix.empty) : KillsBrick ρ π q := by
  classical
  obtain ⟨r,hpr⟩ := Prefix.exists_disjoint hp
  obtain ⟨u,hqu⟩ := Prefix.exists_disjoint hq
  by_cases hrq : Disjoint r.brick q.brick
  · exact kills_disjoint ρ π hrq (kills_disjoint ρ π hpr hk)
  · obtain ⟨x,hxr,hxq⟩ := Set.not_disjoint_iff.mp hrq
    let v := Prefix.common x r q
    have hvr : v.brick ⊆ r.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_left hxr)
    have hvq : v.brick ⊆ q.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_right hxq)
    exact kills_disjoint ρ π hqu.symm
      (kills_disjoint ρ π (hqu.mono_left hvq) (kills_disjoint ρ π (hpr.mono_right hvr) hk))

lemma killed_displacer [Infinite S] {f : localGroup ρ} (hf : f ≠ 1) (hπ : π f=1) :
    ∃ p : Prefix S, p ≠ Prefix.empty ∧ KillsBrick ρ π p := by
  obtain ⟨p,q,a,hd,he⟩ := exists_displaced_brick ρ hf
  have hp : p ≠ Prefix.empty := by
    intro hh
    have hq := Prefix.chart_mem_brick q (fun _ _ => false)
    have hp : q.chart (fun _ _ => false) ∈ p.brick := by rw [hh,Prefix.brick_empty]; trivial
    exact Set.disjoint_left.mp hd hp hq
  let F := π.comp (Localization.hom ρ p)
  have hc (g h : localGroup ρ) : Commute (F g) (F h) := by
    have hcomm : Commute (f * Localization.hom ρ p g * f⁻¹) (Localization.hom ρ p h) :=
      Localization.commute_of_disjoint_support ρ hd.symm _ _
        (Localization.conjugate_outside ρ he g) (Localization.outside ρ p h)
    have hc := hcomm.map π
    simpa only [map_mul,map_inv,hπ,one_mul,mul_one,inv_one,F,MonoidHom.comp_apply] using hc
  have hk : commutator (localGroup ρ) ≤ F.ker := by
    rw [commutator_eq_closure,Subgroup.closure_le]
    rintro _ ⟨g,h,rfl⟩
    change F ⁅g,h⁆=1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_commute]
    exact hc g h
  have ht : (⊤ : Subgroup (localGroup ρ)) ≤ F.ker := by
    rw [← (localGroup_perfect ρ).commutator_eq_top]
    exact hk
  exact ⟨p,hp,fun g => ht (Subgroup.mem_top g)⟩

lemma hom_eq_one_of_kills_proper [Infinite S]
    (hk : ∀ p : Prefix S, p ≠ Prefix.empty → KillsBrick ρ π p) (g : localGroup ρ) : π g=1 := by
  apply PerfectProducer.hom_eq_one ρ π _ g
  intro p q hd h
  obtain ⟨s,_,hs⟩ := PartitionMaps.fresh (fun _ : Unit => p) (fun _ : Unit => q) Prefix.empty
  have he : π (BrickSwap.elem ρ p q hd)=1 := by
    rw [Stationary.split ρ (BrickSwap.stationary ρ hd (hs ()).1 (hs ()).2),map_mul,
      hk _ (Prefix.cut_ne_empty _ _),hk _ (Prefix.cut_ne_empty _ _),one_mul]
  rw [he]
  exact Commute.one_left _

lemma hom_eq_one_of_nontrivial_kernel [Infinite S] {f : localGroup ρ} (hf : f ≠ 1)
    (hπ : π f=1) (g : localGroup ρ) : π g=1 := by
  obtain ⟨p,hp,hk⟩ := killed_displacer ρ π hf hπ
  exact hom_eq_one_of_kills_proper ρ π (fun _ hq => kills_proper ρ π hp hk hq) g
end SimplicityProducer
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
lemma localGroup_nontrivial [Nonempty S] : Nontrivial (localGroup ρ) := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  have hd : Disjoint (Prefix.cut s false).brick (Prefix.cut s true).brick := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Bool.false_ne_true ((Prefix.cut_partition s x).unique hx hy)
  let t := BrickSwap.elem ρ (Prefix.cut s false) (Prefix.cut s true) hd
  have ht : t ≠ 1 := by
    intro h
    let x : Box S := fun _ _ => false
    have he := congrArg (fun g : localGroup ρ => g.val ((Prefix.cut s false).chart x)) h
    change t.val ((Prefix.cut s false).chart x) = (Prefix.cut s false).chart x at he
    rw [show t.val ((Prefix.cut s false).chart x)=(Prefix.cut s true).chart x from
      BrickSwap.elem_left ρ _ _ hd x] at he
    exact Set.disjoint_left.mp hd (Prefix.chart_mem_brick _ x) (he ▸ Prefix.chart_mem_brick _ x)
  exact ⟨⟨t,1,ht⟩⟩

theorem localGroup_simple [Infinite S] : IsSimpleGroup (localGroup ρ) := by
  apply (isSimpleGroup_iff _).mpr
  refine ⟨localGroup_nontrivial ρ,?_⟩
  intro N hN
  let := hN
  by_cases hn : N=⊥
  · exact Or.inl hn
  right
  have he : ∃ f : localGroup ρ, f ∈ N ∧ f ≠ 1 := by
    by_contra hh
    push Not at hh
    apply hn
    apply le_antisymm
    · intro g hg
      exact Subgroup.mem_bot.mpr (hh g hg)
    · exact bot_le
  obtain ⟨f,hf,hf1⟩ := he
  apply top_unique
  intro g _
  apply (QuotientGroup.eq_one_iff g).mp
  exact SimplicityProducer.hom_eq_one_of_nontrivial_kernel ρ (QuotientGroup.mk' N)
    hf1 ((QuotientGroup.eq_one_iff f).mpr hf) g
end TwistedBrin

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageGeometry
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
  [DecidableEq Y] [Group G]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y y', T y*S y'=if y=y' then e else 0) (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point) (he : e≠0)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include φ D e S T ρ ι point hρS hTρ hpoint hφ hρ hι hpt he hTS hSe F₂ F₃ in

theorem simple_geometric_overgroup_of_binary_ring_data_oai
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* Rˣ) (hg : Function.Injective g) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      SimpleFInftyOvergroups.HasTypeFInfty H ∧
        ∃ ν : G →* H, Function.Injective ν := by
  let σ := limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι
  let := limitPoints_infinite φ e S T hTS point hφ hpt he
  obtain ⟨hf,ν,hν⟩ := localGroup_overgroup_of_binary_ring_data φ D e S T hTS hSe ρ ι point
    hρS hTρ hpoint hφ hρ hι hpt he F₂ F₃ A π hπ rel hrel hker g hg
  exact ⟨TwistedBrin.localGroup σ,inferInstance,TwistedBrin.localGroup_nontrivial σ,
    TwistedBrin.localGroup_simple σ,hf,ν,hν⟩
end StageGeometry

end
end

end OAI
end

theorem solution : type_of% @OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data_oai := @OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data_oai
