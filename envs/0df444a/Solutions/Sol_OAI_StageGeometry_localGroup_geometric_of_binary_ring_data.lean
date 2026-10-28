-- Prove2me | solution 1 for OAI.StageGeometry.localGroup_geometric_of_binary_ring_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:07:21.286305+00:00
-- url     : https://prove2.me/submissions/8f306a48-a0f3-45b6-86b3-443012c95107

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So034
import Theorems.Thm_OAI_SimpleFInftyOvergroups_SplittingTorusModel_products
import Theorems.Thm_OAI_StageGeometry_finite_set_model
import Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_localGroup_geometric_of_certificates

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingTorus
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace AscendingTorus

open Monoid.Coprod Multiplicative

universe u

variable {U : Type u} [Group U]

variable {V : Type*} [Group V]

variable {P : Type*} [Group P]

theorem map_relation_eq_one_iff (f : U →* U)
    (q : Monoid.Coprod U (Multiplicative ℤ) →* V) (x : U) :
    q (relation f x) = 1 ↔
      q (inl x) = q (inr (ofAdd 1)) * q (inl (f x)) * (q (inr (ofAdd 1)))⁻¹ := by
  simp only [relation, map_mul, map_inv]
  rw [mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul,
    ← eq_mul_inv_iff_mul_eq]

theorem normalClosure_relations_dense (f : U →* U) (S : Set U)
    (hS : Subgroup.closure S = ⊤) :
    relations f = Subgroup.normalClosure (relation f '' S) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    let N := Subgroup.normalClosure (relation f '' S)
    let q := QuotientGroup.mk' N
    have hconj : q.comp inl =
        (MulAut.conj (q (inr (ofAdd 1)))).toMonoidHom.comp ((q.comp inl).comp f) := by
      apply MonoidHom.eq_of_eqOn_dense hS
      intro x hx
      change q (inl x) = q (inr (ofAdd 1)) * q (inl (f x)) * (q (inr (ofAdd 1)))⁻¹
      apply (map_relation_eq_one_iff f q x).1
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨x, hx, rfl⟩)
    rintro _ ⟨x, rfl⟩
    apply (QuotientGroup.eq_one_iff _).1
    apply (map_relation_eq_one_iff f q x).2
    exact DFunLike.congr_fun hconj x
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, _, rfl⟩
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩

theorem finitelyPresented (f : U →* U) [Group.IsFinitelyPresented U] :
    Group.IsFinitelyPresented (Torus f) := by
  obtain ⟨n, φ, hφ, _⟩ := (inferInstance : Group.IsFinitelyPresented U).out
  have : Group.FG U := Group.fg_of_surjective hφ
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG U)
  apply Group.IsFinitelyPresented.quotient
  exact ⟨relation f '' S, hfin.image _, (normalClosure_relations_dense f S hS).symm⟩

theorem finitelyPresented_of_factorization (f : U →* U)
    (a : U →* P) (b : P →* U) (hf : f = b.comp a)
    [Group.IsFinitelyPresented P] : Group.IsFinitelyPresented (Torus f) := by
  subst f
  have := finitelyPresented (a.comp b)
  exact Group.IsFinitelyPresented.equiv (interleaveEquiv a b).symm

end AscendingTorus

namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

variable {P : Type*} [Group P] [Group.IsFinitelyPresented P]

theorem finitelyPresented_of_factorization (a : U →* P) (b : P →* U)
    (heq : f=b.comp a) : Group.IsFinitelyPresented (Torus f hf) := by
  let _ := AscendingTorus.finitelyPresented_of_factorization f a b heq
  exact Group.IsFinitelyPresented.equiv (presentationEquiv f hf).symm

end AscendingHNN

end

end OAI
end

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

lemma tuple_rep (s : X → X) {α : Type*} [Fintype α] (v : α → Limit s) :
    ∃ (i : ℕ) (w : α → X), ∀ a, v a = of s i (w a) := by
  classical
  choose i x hx using fun a => exists_rep s (v a)
  let k := Finset.univ.sup i
  have hik (a : α) : i a ≤ k := Finset.le_sup (f := i) (Finset.mem_univ a)
  exact ⟨k, fun a => s^[k-i a] (x a), fun a => (hx a).trans (of_advance s _ _ (hik a) _)⟩

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (x : ι → Y) (hx : Function.Injective x)

include hTS hSe hx in
lemma partial_prefix (σ : Equiv.Perm ι) (j : ι) :
    matrixPart S T x σ*S (x j)=S (x (σ j)) := by
  classical
  unfold matrixPart
  rw [Finset.sum_mul]
  have heq (i : ι) : S (x (σ i))*T (x i)*S (x j)=if i=j then S (x (σ j)) else 0 := by
    rw [mul_assoc,hTS]
    by_cases h : i=j
    · subst i; simpa using hSe (x (σ j))
    · rw [ite_eq_right (fun he => h (hx he)),mul_zero,ite_eq_right h]
  simp_rw [heq]
  simp

include hTS hSe hx in
lemma value_prefix (σ : Equiv.Perm ι) (j : ι) :
    value S T x σ*S (x j)=S (x (σ j)) := by
  have h := partial_prefix e S T hTS hSe x hx 1 j
  simp only [Equiv.Perm.one_apply] at h
  simpa [value,add_mul,sub_mul,partial_prefix e S T hTS hSe x hx σ j] using
    (show S (x j)-support S T x*S (x j)+S (x (σ j))=S (x (σ j)) by rw [← partial_one,h]; abel)

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

include D hTS hSe in

theorem beta_tuple_transitivity {ι : Type*} [Fintype ι]
    (x y : ι → Y) (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ q : Q R, ∀ i, action q (beta φ S (x i))=beta φ S (y i) := by
  classical
  let F : Finset Y := Finset.univ.image x ∪ Finset.univ.image y
  let x' : ι → F := fun i => ⟨x i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
  let y' : ι → F := fun i => ⟨y i,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
  have hx' : Function.Injective x' := fun i j h => hx (congrArg Subtype.val h)
  have hy' : Function.Injective y' := fun i j h => hy (congrArg Subtype.val h)
  obtain ⟨η,hη⟩ := Equiv.Perm.exists_extending_pair x' y' hx' hy'
  let v := PrefixPermutation.units e S T hTS hSe (Subtype.val : F → Y) Subtype.val_injective η
  refine ⟨transitionUnits φ D v,fun i => transitionUnits_beta φ D S v (x i) (y i) ?_⟩
  change PrefixPermutation.value S T (Subtype.val : F → Y) η*S (x i)=S (y i)
  have hv := PrefixPermutation.value_prefix e S T hTS hSe
    (Subtype.val : F → Y) Subtype.val_injective η (x' i)
  simpa only [hη] using hv

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

include D hTS hSe in
lemma sigma_tuple_transitivity (hpt : Function.Injective point) (n : ℕ)
    (x y : Fin n → X R) (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ q : Q R, ∀ i, action q (sigma φ S point (x i))=sigma φ S point (y i) :=
  beta_tuple_transitivity φ D e S T hTS hSe (point ∘ x) (point ∘ y) (hpt.comp hx) (hpt.comp hy)

end StageConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.SteinbergFinitePresentation.instFiniteElemFreeGroupRootOptionRelations _root_.OAI.SteinbergFinitePresentation.instFiniteRoot _root_.OAI.SteinbergFinitePresentation.instIsFinitelyPresentedUniversalOfFinite
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

lemma tuple_transitivity (ht : HasImageTupleTransitivity (U := U) s)
    (n : ℕ) (v w : Fin n → Limit s) (hv : Function.Injective v)
    (hw : Function.Injective w) :
    ∃ g : Torus f hf, ∀ a, representation f hf s heq g (v a) = w a := by
  obtain ⟨i,z,hz⟩ := tuple_rep s (Sum.elim v w)
  let x : Fin n → X := fun a => z (.inl a)
  let y : Fin n → X := fun a => z (.inr a)
  have hx (a : Fin n) : v a = of s i (x a) := hz (.inl a)
  have hy (a : Fin n) : w a = of s i (y a) := hz (.inr a)
  have hxi : Function.Injective x := by
    intro a b hab
    apply hv
    rw [hx a,hx b,hab]
  have hyi : Function.Injective y := by
    intro a b hab
    apply hw
    rw [hy a,hy b,hab]
  obtain ⟨u,hu⟩ := ht n x y hxi hyi
  refine ⟨(stable f hf)^(i+1) * embed f hf u * ((stable f hf)^(i+1))⁻¹,fun a => ?_⟩
  simp only [map_mul,map_pow,map_inv,representation_stable,representation_embed]
  have h₀ (x : X) : ((shift s)^(i+1)) (of s 0 x) = of s (i+1) x := by
    simpa only [Nat.zero_add] using shift_pow_of s (i+1) 0 x
  rw [hx,hy,← of_succ s i (x a),← of_succ s i (y a),← h₀ (s (x a))]
  simp only [Equiv.Perm.mul_apply]
  simp only [Equiv.Perm.inv_def,Equiv.symm_apply_apply,basePerm_of]
  simp only [Function.iterate_zero,id_eq,hu,h₀]

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

include hTS hSe hpt in
                                                                                    
lemma limit_tuple_transitivity (n : ℕ) (x y : Fin n → LimitPoints φ S point)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ q : LimitGroup φ D ρ ι hφ hρ hι,
      ∀ j, limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι q (x j)=y j :=
  TorusAction.tuple_transitivity (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
    (sigma φ S point) (fun q x => (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm)
    (sigma_tuple_transitivity φ D e S T hTS hSe point hpt) n x y hx hy

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

namespace Steinberg
section
variable {n R : Type*} [Ring R]
variable (spare : ∀ i j : n, i≠j → ∃ k, i≠k ∧ k≠j)

include spare in
lemma root_mem_normalClosure_span (s : Set R) {a : R} (ha : a∈TwoSidedIdeal.span s)
    (i j : n) (hij : i≠j) : root i j hij a∈Subgroup.normalClosure (rootSet (n:=n) s) := by
  have h : TwoSidedIdeal.span s ≤ coefficients spare (Subgroup.normalClosure (rootSet (n:=n) s)) := by
    apply TwoSidedIdeal.span_le.mpr
    intro r hr
    apply (mem_coefficients spare _ r).mpr
    intro i j hij
    exact Subgroup.subset_normalClosure ⟨i,j,hij,r,hr,rfl⟩
  exact (mem_coefficients _ _ a).mp (h ha) i j hij

variable {S : Type*} [Ring S]
lemma map_surjective (φ : R →ₙ+* S) (hφ : Function.Surjective φ) :
    Function.Surjective (map (n:=n) φ) := by
  intro g
  have h : g∈(map (n:=n) φ).range := by
    apply PresentedGroup.generated_by (relations n S) (map φ).range _ g
    intro r
    obtain ⟨a,ha⟩ := hφ r.coefficient
    refine ⟨root r.i r.j r.different a, ?_⟩
    rw [map_root,ha]
    rfl
  exact h

lemma normalClosure_kernel_le (φ : R →ₙ+* S) :
    Subgroup.normalClosure (rootSet (n:=n) {a | φ a=0})≤(map (n:=n) φ).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i,j,hij,a,ha,rfl⟩
  change map φ (root i j hij a)=1
  rw [map_root,ha,root_zero]

end

section
variable {n R S H : Type*} [Ring R] [Ring S] [_root_.Group H]

lemma descendCoefficients_comp (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (f : Group n R →* H)
    (hker : ∀ i j hij a, φ a=0 → f (root i j hij a)=1) :
    (descendCoefficients φ hφ f hker).comp (map φ)=f := by
  apply hom_ext
  intro i j hij a
  simp only [MonoidHom.comp_apply,map_root,descendCoefficients,lift_root]
  apply root_image_eq φ f hker
  exact Function.surjInv_eq hφ _

theorem ker_map (φ : R →ₙ+* S) (hφ : Function.Surjective φ) :
    (map (n:=n) φ).ker=Subgroup.normalClosure (rootSet (n:=n) {a | φ a=0}) := by
  apply le_antisymm _ (normalClosure_kernel_le φ)
  let N := Subgroup.normalClosure (rootSet (n:=n) {a | φ a=0})
  let f := QuotientGroup.mk' N
  have hk : ∀ i j hij a, φ a=0 → f (root i j hij a)=1 := by
    intro i j hij a ha
    exact QuotientGroup.eq_one_iff _ |>.mpr (Subgroup.subset_normalClosure ⟨i,j,hij,a,ha,rfl⟩)
  have hd := descendCoefficients_comp φ hφ f hk
  intro w hw
  have he : f w=1 := by
    rw [← hd,MonoidHom.comp_apply,MonoidHom.mem_ker.mp hw,map_one]
  exact (QuotientGroup.eq_one_iff _).mp he

variable (spare : ∀ i j : n, i≠j → ∃ k, i≠k ∧ k≠j)

include spare in
                                                                              
theorem ker_map_span (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (s : Set R) (hs : {a | φ a=0}=(TwoSidedIdeal.span s : Set R)) :
    (map (n:=n) φ).ker=Subgroup.normalClosure (rootSet (n:=n) s) := by
  rw [ker_map φ hφ,hs]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i,j,hij,a,ha,rfl⟩
    exact root_mem_normalClosure_span spare s ha i j hij
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨i,j,hij,a,ha,rfl⟩
    exact ⟨i,j,hij,a,TwoSidedIdeal.subset_span ha,rfl⟩

end

variable {n R S : Type*} [Ring R] [Ring S]
variable (spare : ∀ i j : n, i≠j → ∃ k, i≠k ∧ k≠j)

lemma rootSet_finite [Finite n] (s : Set R) (hs : s.Finite) : (rootSet (n:=n) s).Finite := by
  have he : rootSet (n:=n) s=⋃ i, ⋃ j, ⋃ hij : i≠j, root i j hij '' s := by
    ext g
    simp only [rootSet,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_image]
    constructor
    · rintro ⟨i,j,hij,a,ha,rfl⟩; exact ⟨i,j,hij,a,ha,rfl⟩
    · rintro ⟨i,j,hij,a,ha,rfl⟩; exact ⟨i,j,hij,a,ha,rfl⟩
  rw [he]
  exact Set.finite_iUnion (fun i => Set.finite_iUnion (fun j =>
    Set.finite_iUnion (fun hij => hs.image (root i j hij))))

include spare in

theorem finitelyPresented_quotient [Finite n] [_root_.Group.IsFinitelyPresented (Group n R)]
    (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (s : Set R) (hs : s.Finite) (hker : {a | φ a=0}=(TwoSidedIdeal.span s : Set R)) :
    _root_.Group.IsFinitelyPresented (Group n S) := by
  apply _root_.Group.IsFinitelyPresented.of_surjective (map φ) (map_surjective φ hφ)
  exact ⟨rootSet s,rootSet_finite s hs,(ker_map_span spare φ hφ s hker).symm⟩

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergFinitePresentation
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
namespace SteinbergFinitePresentation
open scoped commutatorElement
variable (n α : Type*)

variable (outside : ∀ i j k l : n, ∃ p, p≠i ∧ p≠j ∧ p≠k ∧ p≠l)

include outside in

theorem free_finitelyPresented [Finite n] [Finite α] :
    Group.IsFinitelyPresented (Steinberg.Group n (Coeff α)) :=
  Group.IsFinitelyPresented.equiv (equiv n α outside)

include outside in

theorem finitelyPresented [Finite n] [Finite α] {R : Type*} [Ring R]
    (φ : Coeff α →ₙ+* R) (hφ : Function.Surjective φ)
    (s : Set (Coeff α)) (hs : s.Finite)
    (hker : {a | φ a=0}=(TwoSidedIdeal.span s : Set (Coeff α))) :
    Group.IsFinitelyPresented (Steinberg.Group n R) := by
  let := free_finitelyPresented n α outside
  apply Steinberg.finitelyPresented_quotient (fun i j _ => ?_) φ hφ s hs hker
  obtain ⟨p,hpi,hpj,-,-⟩ := outside i j i j
  exact ⟨p,hpi.symm,hpj⟩

lemma fin_six_outside (i j k l : Fin 6) :
    ∃ p : Fin 6, p≠i ∧ p≠j ∧ p≠k ∧ p≠l := by
  classical
  have hn : ({i,j,k,l} : Finset (Fin 6))≠Finset.univ := by
    apply (Finset.card_lt_iff_ne_univ _).mp
    have h := (Finset.card_le_four (a:=i) (b:=j) (c:=k) (d:=l))
    simp only [Fintype.card_fin]
    omega
  have hp : ∃ p : Fin 6, p∉({i,j,k,l} : Finset (Fin 6)) := by
    by_contra h
    apply hn
    apply Finset.eq_univ_iff_forall.mpr
    simpa only [not_exists,not_not] using h
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hp

theorem rank_six_finitelyPresented [Finite α] {R : Type*} [Ring R]
    (φ : Coeff α →ₙ+* R) (hφ : Function.Surjective φ)
    (s : Set (Coeff α)) (hs : s.Finite)
    (hker : {a | φ a=0}=(TwoSidedIdeal.span s : Set (Coeff α))) :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R) :=
  finitelyPresented (Fin 6) α fin_six_outside φ hφ s hs hker

end SteinbergFinitePresentation
end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryAlgebraPresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace BinaryAlgebraPresentation
variable (A : Type*)

lemma reduction_surjective : Function.Surjective (reduction A) := by
  intro x
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    refine ⟨(c.val : Integral A),?_⟩
    simp only [map_natCast]
    simpa only [map_natCast] using
      congrArg (algebraMap (ZMod 2) (Binary A)) (ZMod.natCast_zmod_val c)
  | grade1 a => exact ⟨FreeAbelianGroup.of (FreeMonoid.of a),reduction_gen A a⟩
  | mul x y hx hy =>
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact ⟨u*v,map_mul _ _ _⟩
  | add x y hx hy =>
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact ⟨u+v,map_add _ _ _⟩

lemma reduction_kernel : TwoSidedIdeal.ker (reduction A) = TwoSidedIdeal.span {2} := by
  let I : TwoSidedIdeal (Integral A) := TwoSidedIdeal.span {2}
  have hI : I ≤ TwoSidedIdeal.ker (reduction A) := by
    apply TwoSidedIdeal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change reduction A 2=0
    simp only [map_ofNat]
    exact CharP.ofNat_eq_zero (Binary A) 2
  let Q := I.ringCon.Quotient
  let q : Integral A →+* Q := I.ringCon.mk'
  have hq (x : Integral A) : q x=0 ↔ x∈I := by
    change x∈TwoSidedIdeal.ker q ↔ x∈I
    rw [TwoSidedIdeal.ker_ringCon_mk']
  let : Nontrivial Q := ⟨⟨0,1,by
    intro h
    have hi : (1 : Integral A)∈I := (hq 1).mp (by simpa using h.symm)
    have hk : reduction A 1=0 := hI hi
    simp at hk⟩⟩
  let : CharP Q 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by
    have : q 2=0 := (hq 2).mpr (TwoSidedIdeal.subset_span (by simp))
    simpa only [map_ofNat,Nat.cast_ofNat] using this)
  let : Algebra (ZMod 2) Q := ZMod.algebra Q 2
  let r : Binary A →ₐ[ZMod 2] Q :=
    FreeAlgebra.lift (ZMod 2) (fun a => q (FreeAbelianGroup.of (FreeMonoid.of a)))
  have gen : ∀ w : FreeMonoid A, r (reduction A (FreeAbelianGroup.of w)) =
      q (FreeAbelianGroup.of w) := by
    have hm : (r.toRingHom.comp (reduction A)).toMonoidHom.comp FreeAbelianGroup.ofMulHom =
        q.toMonoidHom.comp FreeAbelianGroup.ofMulHom := by
      apply FreeMonoid.hom_eq
      intro a
      simp [r]
    intro w
    exact congrArg (fun f : FreeMonoid A →* Q => f w) hm
  have all (x : Integral A) : r (reduction A x)=q x := by
    induction x using FreeAbelianGroup.induction_on with
    | zero => simp
    | of w => exact gen w
    | neg x hx => simpa only [map_neg] using congrArg Neg.neg hx
    | add x y hx hy => simp only [map_add,hx,hy]
  apply le_antisymm _ hI
  intro x hx
  apply (hq x).mp
  change reduction A x=0 at hx
  rw [← all x,hx,map_zero]
variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

lemma kernel_composition (f : R →+* S) (hf : Function.Surjective f)
    (g : S →+* T) (s : Set R) (t : Set S)
    (hfs : TwoSidedIdeal.ker f=TwoSidedIdeal.span s)
    (hgt : TwoSidedIdeal.ker g=TwoSidedIdeal.span t) :
    TwoSidedIdeal.ker (g.comp f)=
      TwoSidedIdeal.span (s ∪ (Function.surjInv hf '' t)) := by
  classical
  let v : S → R := Function.surjInv hf
  have hv : ∀ y, f (v y)=y := Function.surjInv_eq hf
  let J : TwoSidedIdeal R := TwoSidedIdeal.span (s ∪ (v '' t))
  have hsJ : TwoSidedIdeal.span s ≤ J := TwoSidedIdeal.span_mono Set.subset_union_left
  have hlift : ∀ y, y∈TwoSidedIdeal.span t → ∃ x∈J, f x=y := by
    intro y hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y hy =>
      exact ⟨v y,TwoSidedIdeal.subset_span (Or.inr ⟨y,hy,rfl⟩),hv y⟩
    | zero => exact ⟨0,J.zero_mem,map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x',hx',hfx⟩ := hx
      obtain ⟨y',hy',hfy⟩ := hy
      exact ⟨x'+y',J.add_mem hx' hy',by rw [map_add,hfx,hfy]⟩
    | neg x _ hx =>
      obtain ⟨x',hx',hfx⟩ := hx
      exact ⟨-x',J.neg_mem hx',by rw [map_neg,hfx]⟩
    | left_absorb a x _ hx =>
      obtain ⟨x',hx',hfx⟩ := hx
      exact ⟨v a*x',J.mul_mem_left _ _ hx',by rw [map_mul,hv,hfx]⟩
    | right_absorb b x _ hx =>
      obtain ⟨x',hx',hfx⟩ := hx
      exact ⟨x'*v b,J.mul_mem_right _ _ hx',by rw [map_mul,hv,hfx]⟩
  apply le_antisymm
  · intro x hx
    have hx : g (f x)=0 := (TwoSidedIdeal.mem_ker (g.comp f)).mp hx
    have hfx : f x∈TwoSidedIdeal.span t := hgt ▸ (TwoSidedIdeal.mem_ker g).mpr hx
    obtain ⟨y,hy,hfy⟩ := hlift (f x) hfx
    have hsub : x-y∈TwoSidedIdeal.ker f := by
      apply (TwoSidedIdeal.mem_ker f).mpr
      rw [map_sub,hfy,sub_self]
    have hm := J.add_mem (hsJ (hfs ▸ hsub)) hy
    simpa only [sub_add_cancel] using hm
  · apply TwoSidedIdeal.span_le.mpr
    intro x hx
    apply (TwoSidedIdeal.mem_ker (g.comp f)).mpr
    change g (f x)=0
    rcases hx with hx | ⟨y,hy,rfl⟩
    · have hz : f x=0 := (TwoSidedIdeal.mem_ker f).mp
        (hfs.symm ▸ TwoSidedIdeal.subset_span hx)
      rw [hz,map_zero]
    · rw [hv]
      exact (TwoSidedIdeal.mem_ker g).mp (hgt.symm ▸ TwoSidedIdeal.subset_span hy)

theorem integral_presentation
    (π : Binary A →+* R) (hπ : Function.Surjective π)
    (rel : Set (Binary A)) (hrel : rel.Finite)
    (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel) :
    ∃ (q : Integral A →ₙ+* R) (s : Set (Integral A)),
      Function.Surjective q ∧ s.Finite ∧
      {x | q x=0}=(TwoSidedIdeal.span s : Set (Integral A)) := by
  let v := Function.surjInv (reduction_surjective A)
  refine ⟨(π.comp (reduction A)).toNonUnitalRingHom,{2} ∪ (v '' rel),
    hπ.comp (reduction_surjective A),
    (Set.finite_singleton 2).union (hrel.image v),?_⟩
  have hk := kernel_composition (reduction A) (reduction_surjective A)
    π {2} rel (reduction_kernel A) hker
  ext x
  change (π.comp (reduction A)) x=0 ↔ x∈TwoSidedIdeal.span ({2} ∪ (v '' rel))
  rw [←TwoSidedIdeal.mem_ker (π.comp (reduction A)),hk]

theorem rank_six_of_binary_presentation [Finite A]
    (π : Binary A →+* R) (hπ : Function.Surjective π)
    (rel : Set (Binary A)) (hrel : rel.Finite)
    (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel) :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R) := by
  obtain ⟨q,s,hq,hs,hks⟩ := integral_presentation A π hπ rel hrel hker
  exact SteinbergFinitePresentation.rank_six_finitelyPresented A q hq s hs hks

end BinaryAlgebraPresentation

open scoped Pointwise

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
namespace SimpleFInftyOvergroups.SplittingTorusModel
variable {G : Type} [Group G]

theorem finitelyPresented (M : SplittingTorusModel G) : Group.IsFinitelyPresented G := by
  rcases M with @⟨U,P,gU,gP,hP,f,hf,α,b,hb,F₂,F₃,e⟩
  let := AscendingHNN.finitelyPresented_of_factorization f hf α b hb
  exact Group.IsFinitelyPresented.equiv e

end SimpleFInftyOvergroups.SplittingTorusModel

end
end

section

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)

lemma pointwise_eq_fixing (F : Finset S) :
    letI := MulAction.compHom S ρ
    pointwiseStabilizer ρ F = fixingSubgroup A (F : Set S) := by
  let := MulAction.compHom S ρ
  ext a
  exact (mem_fixingSubgroup_iff A).symm

lemma pointwise_empty : pointwiseStabilizer ρ ∅ = ⊤ := by
  ext a
  simp [pointwiseStabilizer]

lemma oligomorphic_of_highly_transitive [Infinite S]
    (ht : ∀ n (x y : Fin n → S), Function.Injective x → Function.Injective y →
      ∃ a : A, ∀ i, ρ a (x i) = y i) : Oligomorphic ρ := by
  classical
  intro n
  let y : Fin n → S := fun i => Infinite.natEmbedding S i.val
  have hy : Function.Injective y := (Infinite.natEmbedding S).injective.comp Fin.val_injective
  let E : Finset S := Finset.univ.image y
  refine ⟨{E},?_⟩
  intro F hF
  let e : F ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hF)
  let x : Fin n → S := fun i => (e.symm i).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  obtain ⟨a,ha⟩ := ht n x y hx hy
  refine ⟨E,Finset.mem_singleton_self _,a,?_⟩
  ext s
  constructor
  · intro hs
    obtain ⟨t,ht,hst⟩ := Finset.mem_map.mp hs
    apply Finset.mem_image.mpr
    refine ⟨e ⟨t,ht⟩,Finset.mem_univ _,?_⟩
    rw [← ha]
    simpa [x] using hst
  · intro hs
    obtain ⟨i,hi,hsi⟩ := Finset.mem_image.mp hs
    exact Finset.mem_map.mpr ⟨x i,(e.symm i).property,(ha i).trans hsi⟩

theorem localGroup_geometric_of_torus_models [Nonempty S]
    (hρ : Function.Injective ρ) (ho : Oligomorphic ρ)
    (hm : ∀ F : Finset S, Nonempty
      (SimpleFInftyOvergroups.SplittingTorusModel (pointwiseStabilizer ρ F))) :
    SimpleFInftyOvergroups.HasTypeFInfty (localGroup ρ) := by
  have hf (F : Finset S) : Group.IsFinitelyPresented (pointwiseStabilizer ρ F) :=
    (hm F).some.finitelyPresented
  let := hf ∅
  let e : pointwiseStabilizer ρ ∅ ≃* A := (MulEquiv.subgroupCongr (pointwise_empty ρ)).trans Subgroup.topEquiv
  let : Group.IsFinitelyPresented A := Group.IsFinitelyPresented.equiv e
  exact Basis.CutBasis.localGroup_geometric_of_certificates hρ ho hf
    (fun F I n => (hm F).some.products I n)
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
theorem localGroup_geometric_of_binary_ring_data_oai
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel) :
    SimpleFInftyOvergroups.HasTypeFInfty
      (TwistedBrin.localGroup (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι)) := by
  let σ := limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  let := BinaryAlgebraPresentation.rank_six_of_binary_presentation A π hπ rel hrel hker
  let := limitPoints_infinite φ e S T hTS point hφ hpt he
  have hσ : Function.Injective σ :=
    limitRepresentation_injective φ D e S T hTS ρ ι point hρS hpoint hφ hρ hι hpt he
  have ho : TwistedBrin.Oligomorphic σ := TwistedBrin.oligomorphic_of_highly_transitive σ
    (fun n x y hx hy => limit_tuple_transitivity φ D e S T hTS hSe ρ ι point hρS hpoint
      hφ hρ hι hpt n x y hx hy)
  apply TwistedBrin.localGroup_geometric_of_torus_models σ hσ ho
  intro F
  obtain ⟨M⟩ := finite_set_model φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ (F : Set (LimitPoints φ S point)) F.finite_toSet
  exact ⟨M.relabel (MulEquiv.subgroupCongr (TwistedBrin.pointwise_eq_fixing σ F)).symm⟩

end StageGeometry

end
end

end OAI
end

theorem solution : type_of% @OAI.StageGeometry.localGroup_geometric_of_binary_ring_data_oai := @OAI.StageGeometry.localGroup_geometric_of_binary_ring_data_oai
