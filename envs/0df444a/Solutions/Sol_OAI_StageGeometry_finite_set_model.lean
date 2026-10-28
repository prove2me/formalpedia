-- Prove2me | solution 1 for OAI.StageGeometry.finite_set_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:05:34.077398+00:00
-- url     : https://prove2.me/submissions/62a8e757-edf2-41cb-bf14-502a70ce3d61

import Mathlib
import Definitions.Def_OAIQ66So034

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

lemma exchange_val (i j : n) (h : i≠j) (d : R) (hd : d*d=d) :
    (exchange i j h d).val=1-Matrix.single i i d-Matrix.single j j d+
      Matrix.single i j d-Matrix.single j i d := by
  simp only [exchange,Units.val_mul,root_val]
  simp [mul_add,add_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,hd,
    ← Matrix.single_neg]
  abel

lemma exchange_move (i j : n) (h : i≠j) (d : R) (hd : d*d=d) (v : Rˣ)
    (hl : d*(v.val-1)=v.val-1) (hr : (v.val-1)*d=v.val-1) :
    exchange i j h d * position i v * (exchange i j h d)⁻¹=position j v := by
  apply (mul_right_cancel_iff).mp
  rw [mul_assoc,inv_mul_cancel,mul_one]
  apply Units.ext
  simp only [Units.val_mul,exchange_val i j h d hd,position_val]
  simp [mul_add,add_mul,sub_mul,mul_sub,
    Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,hl,hr]
  abel

end NoncommElementary

namespace PrefixPermutation
variable {R Y ι : Type*} [Ring R] [DecidableEq Y] [Fintype ι] [DecidableEq ι]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (x : ι → Y) (hx : Function.Injective x)

include hTS hSe hx in
lemma complement_idempotent (ψ : R →ₙ+* R) :
    complement S T x ψ * complement S T x ψ = complement S T x ψ := by
  have hp : ψ (support S T x)*ψ (support S T x)=ψ (support S T x) := by
    rw [← map_mul,support_idempotent e S T hTS hSe x hx]
  unfold complement
  noncomm_ring [hp]

include hTS hSe hx in
lemma complement_prefix (ψ : R →ₙ+* R) (j : ι) :
    complement S T x ψ * ψ (S (x j))=0 := by
  have h := partial_prefix e S T hTS hSe x hx 1 j
  change support S T x*S (x j)=S (x j) at h
  rw [complement,sub_mul,one_mul,← map_mul,h,sub_self]

omit [DecidableEq Y] [DecidableEq ι] in
lemma complement_support (ψ : R →ₙ+* R) (a : R)
    (hS : ∀ j, a*S (x j)=0) (hT : ∀ j, T (x j)*a=0) :
    complement S T x ψ*ψ a=ψ a ∧ ψ a*complement S T x ψ=ψ a := by
  have hl : support S T x*a=0 := by
    simp [support,Finset.sum_mul,mul_assoc,hT]
  have hr : a*support S T x=0 := by
    simp [support,Finset.mul_sum,← mul_assoc,hS]
  constructor
  · rw [complement,sub_mul,one_mul,← map_mul,hl,map_zero,sub_zero]
  · rw [complement,mul_sub,mul_one,← map_mul,hr,map_zero,sub_zero]

end PrefixPermutation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.SteinbergFinitePresentation.instFiniteElemFreeGroupRootOptionRelations _root_.OAI.SteinbergFinitePresentation.instFiniteRoot _root_.OAI.SteinbergFinitePresentation.instIsFinitelyPresentedUniversalOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
variable {R : Type*} [Ring R]

lemma matrix_descended (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (g : NoncommElementary.elementary (R:=R) (n:=Fin 6)) :
    matrix (descended φ D g)=NonunitalCompression.units (matrixCoefficient φ) g.val := by
  obtain ⟨w,rfl⟩ := pi_surjective g
  rw [descended_pi,matrix_map,pi_coe]

lemma matrixCoefficient_position {n : Type*} [Fintype n] [DecidableEq n]
    (φ : R →ₙ+* R) (i : n) (v : Rˣ) :
    NonunitalCompression.units (matrixCoefficient φ) (NoncommElementary.position i v) =
      NoncommElementary.position i (NonunitalCompression.units φ v) := by
  apply Units.ext
  simp only [NonunitalCompression.units_val,NoncommElementary.position_val,
    add_sub_cancel_left]
  change 1+(Matrix.single i i (v.val-1)).map φ = 1+Matrix.single i i (φ (v.val-1))
  rw [Matrix.map_single _ _ _ φ]

theorem matrix_unitLift (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (v : Rˣ) : matrix (unitLift φ D v)=
    NoncommElementary.position (0:Fin 6) (NonunitalCompression.units (φ.comp φ) v) := by
  rw [unitLift,MonoidHom.comp_apply,matrix_descended,NoncommElementary.compressed_coe,
    matrixCoefficient_position,units_comp]

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.StageConstruction.columnMulAction _root_.OAI.SteinbergFinitePresentation.instFiniteElemFreeGroupRootOptionRelations _root_.OAI.SteinbergFinitePresentation.instFiniteRoot _root_.OAI.SteinbergFinitePresentation.instIsFinitelyPresentedUniversalOfFinite
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

lemma block_position (v : Rˣ) :
    Steinberg.matrixBlock (p:=Unit) (NoncommElementary.position (0:Fin 6) v)=
      NoncommElementary.position second v := by
  apply Units.ext
  ext i j
  cases i <;> cases j <;>
    simp [Steinberg.matrixBlock,NoncommElementary.position_val,second,
      Matrix.single,Matrix.fromBlocks,Matrix.one_apply]

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

lemma block_lift (v : Rˣ) :
    (block (Steinberg.unitLift φ D v)).val=
      NoncommElementary.position second (NonunitalCompression.units (φ.comp φ) v) := by
  rw [block_matrix,Steinberg.matrix_unitLift,block_position]

lemma exchange_lift (d : R) (hd : d*d=d) (v : Rˣ)
    (hl : d*(φ (φ (v.val-1)))=φ (φ (v.val-1)))
    (hr : φ (φ (v.val-1))*d=φ (φ (v.val-1))) :
    exchange d*transitionUnits φ D v*(exchange d)⁻¹=block (Steinberg.unitLift φ D v) := by
  apply Subtype.ext
  change NoncommElementary.exchange first second first_ne_second d *
    (transitionUnits φ D v).val * (NoncommElementary.exchange first second first_ne_second d)⁻¹=_
  rw [transitionUnits_val,block_lift]
  apply NoncommElementary.exchange_move _ _ _ _ hd
  · simpa only [NonunitalCompression.units_val,add_sub_cancel_left,
      NonUnitalRingHom.comp_apply] using hl
  · simpa only [NonunitalCompression.units_val,add_sub_cancel_left,
      NonUnitalRingHom.comp_apply] using hr

variable {ι : Type*}

lemma stabilizerBlock_val (c : ι → R) (a : Q R) (d : R)
    (hc : ∀ i, d*c i=0) (g : Steinberg.Group (Fin 6) R) :
    (stabilizerBlock c a d hc g).val=a*(exchange d)⁻¹*block g*exchange d*a⁻¹ := by
  change (a*(exchange d)⁻¹)*block g*(a*(exchange d)⁻¹)⁻¹=_
  group

lemma stabilizerBlock_lift (c : ι → R) (a : Q R) (d : R)
    (hc : ∀ i, d*c i=0) (hd : d*d=d) (v : Rˣ)
    (hl : d*(φ (φ (v.val-1)))=φ (φ (v.val-1)))
    (hr : φ (φ (v.val-1))*d=φ (φ (v.val-1))) :
    (stabilizerBlock c a d hc (Steinberg.unitLift φ D v)).val=
      a * transitionUnits φ D v * a⁻¹ := by
  rw [stabilizerBlock_val,← exchange_lift φ D d hd v hl hr]
  group

end StageConstruction

namespace StageConstruction
variable {R : Type*} [Ring R]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

variable {ι : Type*} (c : ι → R) (a : Q R)

variable {Y : Type*} [DecidableEq Y] [Fintype ι] [DecidableEq ι]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (x : ι → Y) (hx : Function.Injective x)

include hTS hSe hx in

theorem stabilizer_factor
    (v : compressedFixing φ (S ∘ x) a →* Rˣ)
    (hvS : ∀ u i, (v u).val*S (x i)=S (x i))
    (hvT : ∀ u i, T (x i)*(v u).val=T (x i)) :
    ∃ (α : compressedFixing φ (S ∘ x) a →* Steinberg.Group (Fin 6) R)
      (b : Steinberg.Group (Fin 6) R →* compressedFixing φ (S ∘ x) a),
      b.comp α=stabilizerEnd φ D (S ∘ x) a v hvS := by
  let d := PrefixPermutation.complement S T x (φ.comp φ)
  have hd : d*d=d := PrefixPermutation.complement_idempotent e S T hTS hSe x hx (φ.comp φ)
  have hc : ∀ i, d*φ (φ (S (x i)))=0 :=
    PrefixPermutation.complement_prefix e S T hTS hSe x hx (φ.comp φ)
  refine ⟨(Steinberg.unitLift φ D).comp v,
    stabilizerBlock (fun i => φ (φ (S (x i)))) a d hc, ?_⟩
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  simp only [MonoidHom.comp_apply,stabilizerEnd_val]
  have h := PrefixPermutation.complement_support S T x (φ.comp φ) ((v u).val-1)
    (fun i => by rw [sub_mul,one_mul,hvS u i,sub_self])
    (fun i => by rw [mul_sub,mul_one,hvT u i,sub_self])
  exact stabilizerBlock_lift φ D (fun i => φ (φ (S (x i)))) a d hc hd (v u) h.1 h.2

end StageConstruction

namespace StageConstruction
variable {R : Type*} [Ring R]

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

end StageConstruction

end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace StageGeometry
open StageConstruction

variable {R Y W : Type} [Ring R] [Group W] [MulAction W Y]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (S : Y → R) (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι)

variable {J : Type} (z : J → X R) (a : Q R)
variable (ha : ∀ j, a • shift φ S point (z j) = z j)

variable (hs : Function.Injective (shift φ S point))

include ha in
lemma compressed_fixed (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    (q : Q R) • z j = z j := by
  have h := q.property j
  change (q : Q R) • (a • shift φ S point (z j)) = a • shift φ S point (z j) at h
  rwa [ha j] at h

include hpoint ha in
lemma compressed_point_fixed (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    ι q • point (z j) = point (z j) := by
  rw [hpoint,compressed_fixed φ S point z a ha q j]

include hρS hpoint ha in
lemma units_prefix (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    (compressedUnits φ S ρ ι point z a q).val*S (point (z j))=S (point (z j)) := by
  change (ρ (ι q)).val * S (point (z j)) = _
  rw [hρS,compressed_point_fixed φ S ι point hpoint z a ha q j]

variable (T : Y → R) (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
include hTρ hpoint ha in
lemma units_suffix (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    T (point (z j))*(compressedUnits φ S ρ ι point z a q).val=T (point (z j)) := by
  change T (point (z j)) * (ρ (ι q)).val = _
  rw [hTρ]
  congr 1
  apply inv_smul_eq_iff.mpr
  exact (compressed_point_fixed φ S ι point hpoint z a ha q j).symm

variable (K : Type) [CommRing K] (F : PairDiagrams K ι point)

variable [Fintype J] [DecidableEq J] [DecidableEq Y]
variable (e : R) (hTS : ∀ y y', T y*S y'=if y=y' then e else 0)
variable (hSe : ∀ y, S y*e=S y) (hz : Function.Injective z)
variable (hpt : Function.Injective point)

include ha hs hρS hpoint hTρ hTS hSe hz hpt in

theorem factor :
    ∃ (α : base φ D S ρ ι point hρS hpoint hφ hρ hι z a →*
        Steinberg.Group (Fin 6) R)
      (b : Steinberg.Group (Fin 6) R →*
        base φ D S ρ ι point hρS hpoint hφ hρ hι z a),
      b.comp α = endomorphism φ D S ρ ι point hρS hpoint hφ hρ hι z a ha := by
  let E := baseEquiv φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs
  obtain ⟨α,b,hb⟩ := stabilizer_factor φ D a e S T hTS hSe (point ∘ z)
    (hpt.comp hz) (compressedUnits φ S ρ ι point z a)
    (units_prefix φ S ρ ι point hρS hpoint z a ha)
    (units_suffix φ S ρ ι point hpoint z a ha T hTρ)
  refine ⟨α.comp E.toMonoidHom,E.symm.toMonoidHom.comp b,?_⟩
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  have h := congrArg (fun f => f (E u)) hb
  exact congrArg (fun q : compressedFixing φ (fun j => S (point (z j))) a => q.val) h

end StageGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HomStabilizer
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace SimpleFInftyOvergroups

attribute [instance] SplittingTorusModel.groupU SplittingTorusModel.groupP
  SplittingTorusModel.finitePresentation

end SimpleFInftyOvergroups

namespace StageGeometry
open StageConstruction
variable {R Y W : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y] [DecidableEq Y]
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

theorem finite_tuple_model [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (n : ℕ) (y : Fin n → LimitPoints φ S point) (hy : Function.Injective y) :
    Nonempty (SimpleFInftyOvergroups.SplittingTorusModel
      (HomStabilizer.fixedTuple
        (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) y)) := by
  have hs := sigma_injective φ e S T hTS point he hφ hpt
  let : Infinite (X R) := stagePoints_infinite φ e S T hTS point hφ hpt he
  let x : Fin n → X R := fun i => Infinite.natEmbedding (X R) i.val
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    exact (Infinite.natEmbedding (X R)).injective hij
  let z := sigma φ S point ∘ x
  have hz : Function.Injective z := hs.comp hx
  obtain ⟨a,ha⟩ := sigma_tuple_transitivity φ D e S T hTS hSe point hpt n z x hz hx
  obtain ⟨α,b,hb⟩ := factor φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs T hTρ
    e hTS hSe hz hpt
  let w : Fin n → LimitPoints φ S point := SequentialLimit.of (sigma φ S point) 0 ∘ z
  have hw : Function.Injective w := (SequentialLimit.of_injective _ hs 0).comp hz
  obtain ⟨q,hq⟩ := limit_tuple_transitivity φ D e S T hTS hSe ρ ι point hρS hpoint
    hφ hρ hι hpt n w y hw hy
  refine ⟨{
    U := base φ D S ρ ι point hρS hpoint hφ hρ hι z a
    P := Steinberg.Group (Fin 6) R
    f := endomorphism φ D S ρ ι point hρS hpoint hφ hρ hι z a ha
    injective := endomorphism_injective φ D S ρ ι point hρS hpoint hφ hρ hι z a ha
    α := α
    b := b
    factorization := hb.symm
    splitting₂ := splittings φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs (ZMod 2) F₂
    splitting₃ := splittings φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs (ZMod 3) F₃
    identification := (TorusStabilizer.torusEquiv (trans φ D ρ ι)
      (transInjective φ D ρ ι hφ hρ hι) (shift φ S point)
      (compatible φ D S ρ ι point hρS hpoint) z a ha).trans
      (HomStabilizer.conjugateTuple
        (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) w y q hq) }⟩

include hTS hSe hTρ hpt he F₂ F₃ in
theorem finite_set_model_oai [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (s : Set (LimitPoints φ S point)) (hs : s.Finite) :
    letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
    Nonempty (SimpleFInftyOvergroups.SplittingTorusModel
      (fixingSubgroup (LimitGroup φ D ρ ι hφ hρ hι) s)) := by
  classical
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  let := hs.fintype
  let E := Fintype.equivFin s
  let y : Fin (Fintype.card s) → LimitPoints φ S point := fun i => (E.symm i).val
  have hy : Function.Injective y := Subtype.val_injective.comp E.symm.injective
  have hyS : Set.range y = s := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact (E.symm i).property
    · intro hx
      exact ⟨E ⟨x,hx⟩,congrArg Subtype.val (E.symm_apply_apply ⟨x,hx⟩)⟩
  obtain ⟨M⟩ := finite_tuple_model φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ (Fintype.card s) y hy
  exact ⟨M.relabel (HomStabilizer.enumeratedSubset y s hyS)⟩

end StageGeometry

end

end OAI
end

theorem solution : type_of% @OAI.StageGeometry.finite_set_model_oai := @OAI.StageGeometry.finite_set_model_oai
