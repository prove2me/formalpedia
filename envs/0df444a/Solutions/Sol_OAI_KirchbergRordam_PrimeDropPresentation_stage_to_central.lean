-- Prove2me | solution 1 for OAI.KirchbergRordam.PrimeDropPresentation.stage_to_central
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:29:31.514979+00:00
-- url     : https://prove2.me/submissions/f79a902c-c986-46e0-bada-623b9c83f177

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr013
import Theorems.Thm_OAI_KirchbergRordam_GenericRW_FullSquareZero_exists_full_square_zero

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DetectingSpaces
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PrimitiveSeparation.quotientNormedAlgebra _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace


open scoped BigOperators
open Set Module

universe uQuot


open Topology
namespace KirchbergRordam.GenericRW
namespace DetectingSpace


variable {D : Type*} [CStarAlgebra D]


lemma closedCommutatorIdeal_eq_top (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    closedCommutatorIdeal (D := D) = ⊤ := by
  by_contra h
  have : Nontrivial (CommutativeQuotient D) := Ideal.Quotient.nontrivial_iff.mpr h
  obtain ⟨χ, _⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero
    (not_isUnit_zero : ¬ IsUnit (0 : CommutativeQuotient D))
  let f : D →ₐ[ℂ] ℂ := (WeakDual.CharacterSpace.equivAlgHom χ).comp
    (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)))
  let : StarHomClass (D →ₐ[ℂ] ℂ) D ℂ := AlgHomClass.instStarHomClass
  exact hD.false ({toAlgHom := f, map_star' := map_star f} : D →⋆ₐ[ℂ] ℂ)


lemma commutatorIdeal_eq_top (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    commutatorIdeal (D := D) = ⊤ := by
  have h1 : (1 : D) ∈ closure (commutatorIdeal (D := D) : Set D) := by
    change (1 : D) ∈ closedCommutatorIdeal
    rw [closedCommutatorIdeal_eq_top hD]
    trivial
  obtain ⟨x, hx, hnear⟩ := Metric.mem_closure_iff.mp h1 1 zero_lt_one
  have hu : IsUnit x := by
    have hnorm : ‖1 - x‖ < 1 := by simpa only [dist_eq_norm] using hnear
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm
  have ht := (commutatorIdeal (D := D)).asIdeal.eq_top_of_isUnit_mem hx hu
  apply le_antisymm le_top
  intro x _
  change x ∈ (commutatorIdeal (D := D)).asIdeal
  rw [ht]
  trivial


end DetectingSpace


end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_States
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


open NormedSpace
open scoped ComplexOrder


open scoped ComplexOrder
namespace KirchbergRordam.GenericRW
namespace PureStates
variable (A : Type*) [CStarAlgebra A]

lemma normStates_compact : IsCompact (normStates A) := by
  have h := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous (1 : A)) (continuous_const (y := (1 : ℂ))))
  convert h using 1
  ext φ
  simp [normStates, Metric.mem_closedBall]

variable [Nontrivial A]

lemma normStates_nonempty : (normStates A).Nonempty := by
  obtain ⟨φ, hφ, h1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  refine ⟨(StrongDual.toWeakDual φ), hφ.le, ?_⟩
  simpa using h1


theorem exists_pure : ∃ φ : A →L[ℂ] ℂ, IsPure A φ := by
  obtain ⟨φ, hφ⟩ := (normStates_compact A).extremePoints_nonempty (normStates_nonempty A)
  exact ⟨φ.toStrongDual, hφ⟩

end PureStates
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Representations
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder


open scoped InnerProductSpace
namespace KirchbergRordam.GenericRW
namespace Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


lemma positive_zero_of_square_zero (f : A →ₚ[ℂ] ℂ) (a : A)
    (hz : f (star a * a) = 0) : f a = 0 := by
  have hvec : gnsVector f a = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [gnsVector_inner] using hz
  have hinner := gnsVector_inner f 1 a
  simpa only [hvec, inner_zero_right, star_one, one_mul] using hinner.symm

end Representations

universe u

attribute [instance] IrreducibleRepresentation.normed IrreducibleRepresentation.inner
  IrreducibleRepresentation.complete IrreducibleRepresentation.nontrivial


theorem exists_irreducible_representation (A : Type u) [CStarAlgebra A] [Nontrivial A] :
    Nonempty (IrreducibleRepresentation A) := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  obtain ⟨φ, hp⟩ := PureStates.exists_pure A
  exact ⟨Representations.pureRepresentation φ hp⟩

end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Fullness
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace


namespace KirchbergRordam.GenericRW
namespace PrimitiveSeparation
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (I : Ideal A) [I.IsTwoSided] [IsClosed (I : Set A)]

lemma quotient_norm_one (hI : I ≠ ⊤) : ‖(1 : A ⧸ I)‖ = 1 := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  apply le_antisymm _ (one_le_norm_one (A ⧸ I))
  change ‖(Submodule.Quotient.mk (1 : A) : A ⧸ I)‖ ≤ 1
  simpa only [norm_one] using Submodule.Quotient.norm_mk_le I (1 : A)


omit [Nontrivial A] [I.IsTwoSided] [IsClosed (I : Set A)] in
lemma stateFace_compact : IsCompact (stateFace I) :=
  (PureStates.normStates_compact A).inter_right
    (by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun _ =>
        isClosed_eq (WeakDual.eval_continuous a) continuous_const)

lemma stateFace_nonempty (hI : I ≠ ⊤) : (stateFace I).Nonempty := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨f, hfn, hf1⟩ := exists_dual_vector ℂ (1 : A ⧸ I) (by rw [quotient_norm_one I hI]; exact one_ne_zero)
  have hf1 : f 1 = 1 := by simpa [quotient_norm_one I hI] using hf1
  let g := f.comp (quotientCLM I)
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound (by norm_num)
    intro a
    have hq : ‖quotientCLM I a‖ ≤ ‖a‖ := Submodule.Quotient.norm_mk_le I a
    change ‖f (quotientCLM I a)‖ ≤ 1 * ‖a‖
    calc
      ‖f (quotientCLM I a)‖ ≤ ‖f‖ * ‖quotientCLM I a‖ := f.le_opNorm _
      _ ≤ 1 * ‖a‖ := by rw [hfn, one_mul, one_mul]; exact hq
  refine ⟨StrongDual.toWeakDual g, ⟨hg, ?_⟩, ?_⟩
  · change f (Ideal.Quotient.mk I 1) = 1
    simpa only [map_one] using hf1
  · intro a ha
    change f (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

variable [PartialOrder A] [StarOrderedRing A]

omit [I.IsTwoSided] [IsClosed (I : Set A)] in
lemma stateFace_isFace (φ ψ χ : WeakDual ℂ A) (hφ : ∀ a ∈ I, φ a = 0)
    (hψ : ψ ∈ PureStates.normStates A) (hχ : χ ∈ PureStates.normStates A)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (he : s • ψ + t • χ = φ) :
    (∀ a ∈ I, ψ a = 0) ∧ (∀ a ∈ I, χ a = 0) := by
  have hψp (a : A) (ha : 0 ≤ a) : 0 ≤ ψ a :=
    States.eval_nonneg ψ.toStrongDual hψ.1 hψ.2 a ha
  have hχp (a : A) (ha : 0 ≤ a) : 0 ≤ χ a :=
    States.eval_nonneg χ.toStrongDual hχ.1 hχ.2 a ha
  have hz (a : A) (ha : a ∈ I) : ψ (star a * a) = 0 ∧ χ (star a * a) = 0 := by
    have hpa := hψp (star a * a) (star_mul_self_nonneg a)
    have hca := hχp (star a * a) (star_mul_self_nonneg a)
    have he' := congrArg (fun f : WeakDual ℂ A => (f (star a * a)).re) he
    have hf := hφ (star a * a) (I.mul_mem_left _ ha)
    change ((s • ψ (star a * a) + t • χ (star a * a)) : ℂ).re = (φ (star a * a)).re at he'
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at he'
    rw [hf, Complex.zero_re] at he'
    have hp0 : (ψ (star a * a)).re = 0 := by
      nlinarith [(Complex.nonneg_iff.mp hpa).1, (Complex.nonneg_iff.mp hca).1]
    have hc0 : (χ (star a * a)).re = 0 := by
      nlinarith [(Complex.nonneg_iff.mp hpa).1, (Complex.nonneg_iff.mp hca).1]
    constructor <;> apply Complex.ext
    · exact hp0
    · exact (Complex.nonneg_iff.mp hpa).2.symm
    · exact hc0
    · exact (Complex.nonneg_iff.mp hca).2.symm
  constructor
  · intro a ha
    exact Representations.positive_zero_of_square_zero
      (PositiveLinearMap.mk₀ ψ.toStrongDual.toLinearMap hψp) a (hz a ha).1
  · intro a ha
    exact Representations.positive_zero_of_square_zero
      (PositiveLinearMap.mk₀ χ.toStrongDual.toLinearMap hχp) a (hz a ha).2


theorem exists_pure_annihilating (hI : I ≠ ⊤) :
    ∃ φ : A →L[ℂ] ℂ, PureStates.IsPure A φ ∧ ∀ a ∈ I, φ a = 0 := by
  obtain ⟨φ, hφ⟩ := (stateFace_compact I).extremePoints_nonempty (stateFace_nonempty I hI)
  refine ⟨φ.toStrongDual, ⟨hφ.1.1, ?_⟩, hφ.1.2⟩
  intro ψ hψ χ hχ he
  obtain ⟨s, t, hs, ht, hst, heq⟩ := he
  obtain ⟨hψI, hχI⟩ := stateFace_isFace I φ ψ χ hφ.1.2 hψ hχ s t hs ht heq
  exact hφ.2 ⟨hψ, hψI⟩ ⟨hχ, hχI⟩ ⟨s, t, hs, ht, hst, heq⟩

omit [IsClosed (I : Set A)] in
lemma pureRepresentation_annihilates (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : ∀ a ∈ I, φ a = 0) (a : A) (ha : a ∈ I) :
    (Representations.pureRepresentation φ hp).representation a = 0 := by
  let f := Representations.stateOfPure φ hp
  have hv (b : A) : Representations.gnsVector f (a * b) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [Representations.gnsVector_inner]
    exact hφ _ (I.mul_mem_left _ (I.mul_mem_right _ ha))
  apply ContinuousLinearMap.ext
  intro x
  have hd := Representations.gns_cyclic f
  apply hd.induction_on (p := fun x => f.gnsStarAlgHom a x = 0) x
  · exact isClosed_eq ((f.gnsStarAlgHom a).continuous) continuous_const
  · intro b
    simp only [Representations.gnsVector_apply, mul_one]
    exact hv b


theorem exists_irreducible_annihilating (hI : I ≠ ⊤) :
    ∃ ρ : IrreducibleRepresentation A, ∀ a ∈ I, ρ.representation a = 0 := by
  obtain ⟨φ, hp, hφ⟩ := exists_pure_annihilating I hI
  exact ⟨Representations.pureRepresentation φ hp,
    fun a ha => pureRepresentation_annihilates I φ hp hφ a ha⟩

end PrimitiveSeparation
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.Fullness
variable {A : Type*} [CStarAlgebra A]


lemma eq_top_of_closedIdeal_eq_top (I : TwoSidedIdeal A) (hI : closedIdeal I = ⊤) : I = ⊤ := by
  have h1 : (1 : A) ∈ closure (I : Set A) := by
    change (1 : A) ∈ closedIdeal I
    rw [hI]
    trivial
  obtain ⟨x, hx, hnear⟩ := Metric.mem_closure_iff.mp h1 1 zero_lt_one
  have hu : IsUnit x := by
    have hnorm : ‖1 - x‖ < 1 := by simpa only [dist_eq_norm] using hnear
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm
  have ht := I.asIdeal.eq_top_of_isUnit_mem hx hu
  apply le_antisymm le_top
  intro x _
  change x ∈ I.asIdeal
  rw [ht]
  trivial


lemma full_iff_closed (a : A) : IsFull a ↔ closedIdeal (TwoSidedIdeal.span {a}) = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x hx
    apply subset_closure
    rw [show TwoSidedIdeal.span {a} = ⊤ from h]
    trivial
  · exact eq_top_of_closedIdeal_eq_top _

lemma full_of_survives [Nontrivial A]
    (a : A) (h : ∀ π : IrreducibleRepresentation A, π.representation a ≠ 0) : IsFull a := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  apply (full_iff_closed a).mpr
  by_contra hn
  obtain ⟨π, hπ⟩ := PrimitiveSeparation.exists_irreducible_annihilating
    (closedIdeal (TwoSidedIdeal.span {a})) hn
  exact h π (hπ a (subset_closure (TwoSidedIdeal.subset_span rfl)))

lemma full_ne_zero [Nontrivial A] {a : A} (ha : IsFull a) : a ≠ 0 := by
  intro he
  subst a
  have h : (1 : A) ∈ TwoSidedIdeal.span {0} := by
    rw [show TwoSidedIdeal.span {(0 : A)} = ⊤ from ha]
    exact TwoSidedIdeal.mem_top A
  have hh : TwoSidedIdeal.span ({0} : Set A) ≤ ⊥ := TwoSidedIdeal.span_le.mpr (by simp)
  exact one_ne_zero ((TwoSidedIdeal.mem_bot _).mp (hh h))

lemma full_survives {B : Type*} [CStarAlgebra B] [Nontrivial B]
    {a : A} (ha : IsFull a) (φ : A →⋆ₐ[ℂ] B) : φ a ≠ 0 := by
  intro hz
  have hk : TwoSidedIdeal.span {a} ≤ TwoSidedIdeal.ker φ.toRingHom :=
    TwoSidedIdeal.span_le.mpr (Set.singleton_subset_iff.mpr ((TwoSidedIdeal.mem_ker _).mpr hz))
  have h1 : (1 : A) ∈ TwoSidedIdeal.span {a} := by
    rw [show TwoSidedIdeal.span {a} = ⊤ from ha]
    exact TwoSidedIdeal.mem_top A
  have hz1 := (TwoSidedIdeal.mem_ker _).mp (hk h1)
  exact one_ne_zero (by simpa only [map_one] using hz1)

end KirchbergRordam.GenericRW.Fullness
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SpatialTensor
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace


open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.GenericRW.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace H] [CompleteSpace K]

lemma left_right_commute (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    Commute (left (K := K) T) (right (H := H) S) := by
  change map T 1 * map 1 S = map 1 S * map T 1
  rw [← map_mul, ← map_mul]
  simp

end KirchbergRordam.GenericRW.Spatial

namespace KirchbergRordam.GenericRW
namespace MaxTensor
universe u v
variable (A : Type u) (B : Type v) [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]
omit [Nontrivial A] [Nontrivial B] in
lemma nontrivial_of_representations
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial H] [Nontrivial K]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    Nontrivial (Algebra A B) := by
  let φ : A →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    (Spatial.left (K := K)).comp π
  let ψ : B →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    (Spatial.right (H := H)).comp ρ
  have hc : ∀ a b, Commute (φ a) (ψ b) := fun a b =>
    Spatial.left_right_commute (π a) (ρ b)
  let χ : Algebra A B →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    lift (A := A) (B := B)
      (C := Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) φ ψ hc
  exact χ.toRingHom.domain_nontrivial
instance instNontrivialAlgebra : Nontrivial (Algebra A B) := by
  obtain ⟨π⟩ := exists_irreducible_representation A
  obtain ⟨ρ⟩ := exists_irreducible_representation B
  exact nontrivial_of_representations A B π.representation ρ.representation
instance powerPack_nontrivial (D : Type u) [CStarAlgebra D] [Nontrivial D] (n : ℕ) :
    Nontrivial (powerPack D n) := by
  induction n with
  | zero => exact inferInstanceAs (Nontrivial D)
  | succ n ih =>
    let : Nontrivial (powerPack D n) := ih
    exact inferInstanceAs (Nontrivial (Algebra D (powerPack D n)))
end MaxTensor
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.MaxTensor
universe u
variable (D : Type u) [CStarAlgebra D]


theorem exists_joinPower (n m : ℕ) :
    Nonempty (Algebra (powerPack D n) (powerPack D m) →⋆ₐ[ℂ] (powerPack D (n+m+1))) := by
  induction n with
  | zero =>
    rw [Nat.zero_add]
    exact ⟨StarAlgHom.id ℂ (Algebra D (powerPack D m))⟩
  | succ n ih =>
    obtain ⟨φ⟩ := ih
    let ψ := (map (StarAlgHom.id ℂ D) φ).comp
      (TripleTensor.reassociate (A := D) (B := powerPack D n) (C := powerPack D m))
    have he : n + 1 + m + 1 = (n + m + 1) + 1 := by omega
    rw [he]
    exact ⟨ψ⟩
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.Fullness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]
lemma full_map {a : A} (ha : IsFull a) (φ : A →⋆ₐ[ℂ] B) : IsFull (φ a) := by
  apply full_of_survives
  intro π
  exact full_survives ha (π.representation.comp φ)
end KirchbergRordam.GenericRW.Fullness

namespace KirchbergRordam.GenericRW.FullSquareZero
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]


variable {A : Type u} [CStarAlgebra A] [Nontrivial A]


theorem normalize {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {y : A} (hyz : y * y = 0) (hyfull : IsFull y) :
    ∃ v : A, v * v = 0 ∧ IsFull v ∧ ‖v‖ = 1 := by
  have hy : y ≠ 0 := full_ne_zero hyfull
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  refine ⟨‖y‖⁻¹ • y, ?_, ?_, ?_⟩
  · simp only [smul_mul_assoc, mul_smul_comm, hyz, smul_zero]
  · apply full_of_survives
    intro π he
    have hm : π.representation (‖y‖⁻¹ • y) = ‖y‖⁻¹ • π.representation y :=
      (π.representation.toLinearMap.restrictScalars ℝ).map_smul _ _
    rw [hm] at he
    exact full_survives hyfull π.representation ((smul_eq_zero.mp he).resolve_left (inv_ne_zero hn))
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

end KirchbergRordam.GenericRW.FullSquareZero
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FunctionalCalculus
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW


section
variable {A : Type*} [CStarAlgebra A]


namespace CuntzBelow

omit instSize in
lemma of_approx.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b : A} (h : ∀ ε > 0, ∃ x : A, ‖a - star x * b * x‖ < ε) :
    CuntzBelow a b := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨x, hx⟩ := h ε hε
  exact ⟨_, ⟨x, rfl⟩, by simpa only [dist_eq_norm] using hx⟩

omit instSize in
lemma of_eq.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b x : A} (h : star x * b * x = a) : CuntzBelow a b :=
  subset_closure ⟨x, h⟩

@[refl] lemma refl (a : A) : CuntzBelow a a := of_eq (x := 1) (by simp)

lemma trans {a b c : A} (hab : CuntzBelow a b) (hbc : CuntzBelow b c) : CuntzBelow a c := by
  apply of_approx
  intro ε hε
  obtain ⟨x, hx⟩ := hab.approx (half_pos hε)
  obtain ⟨y, hy⟩ := hbc.approx (div_pos (half_pos hε) (by positivity : (0:ℝ) < ‖x‖^2+1))
  refine ⟨y*x, ?_⟩
  have he : a - star (y*x) * c * (y*x) =
      (a - star x*b*x) + star x * (b-star y*c*y) * x := by
    rw [star_mul]
    noncomm_ring
  have hn : ‖star x * (b-star y*c*y) * x‖ ≤ ‖x‖^2 * ‖b-star y*c*y‖ := by
    calc
      _ ≤ (‖star x‖ * ‖b-star y*c*y‖) * ‖x‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = _ := by rw [norm_star]; ring
  have hy' : (‖x‖^2+1)*‖b-star y*c*y‖ < ε/2 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < ‖x‖^2+1)).mp hy
    nlinarith
  rw [he]
  exact (norm_add_le _ _).trans_lt (by nlinarith [norm_nonneg (b-star y*c*y)])

end CuntzBelow
end

end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixSimplex
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.CubeWeights
open scoped BigOperators
variable {n : ℕ}

lemma localized_normalized (t : Punctured n) {δ : ℝ} (hδ : 0<δ) (j : Fin (n+1))
    (hj : δ<(t.1 j:ℝ)) (hi : ∀ i,i≠j → (t.1 i:ℝ)<δ/2) :
    normalized t=CoordinateSimplex.vertex j := by
  have hd : radius t.1=(t.1 j:ℝ) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      by_cases he : i=j
      · subst i; exact le_rfl
      · linarith [hi i he]
    · exact coord_le_radius _ _
  have hpos : 0<(t.1 j:ℝ) := hδ.trans hj
  have hw (i : Fin (n+1)) : weight t i=if i=j then 1/2 else 0 := by
    unfold weight
    rw [hd]
    by_cases he : i=j
    · subst i; rw [div_self hpos.ne']; norm_num
    · rw [ite_eq_right he,max_eq_right]
      have hh : (t.1 i:ℝ)/(t.1 j:ℝ)<1/2 := (div_lt_iff₀ hpos).mpr (by linarith [hi i he])
      linarith
  have htotal : total t=1/2 := by simp [total,hw]
  ext i
  rw [normalized_apply,hw,htotal]
  by_cases he : i=j <;> simp [he,eq_comm]

omit instSize instPauliData in
lemma g_pos
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) (h : 0<g δ t) : (t:ℝ)<δ/2 := by
  have hp : 0<1-2*(t:ℝ)/δ := (lt_max_iff.mp h).resolve_right (lt_irrefl _)
  have hh : 2*(t:ℝ)/δ<1 := by linarith
  have := (div_lt_one hδ).mp hh
  linarith
omit instSize instPauliData in
lemma g_of_large
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) (h : δ≤(t:ℝ)) : g δ t=0 := by
  apply max_eq_right
  have : 1≤2*(t:ℝ)/δ := (one_le_div hδ).mpr (by linarith)
  linarith

lemma H_of_large {δ : ℝ} (hδ : 0<δ) (t : Cube n) (j : Fin (n+1)) (h : δ≤(t j:ℝ)) : H δ t=1 := by
  have hz : ∏ i,g δ (t i)=0 := Finset.prod_eq_zero (Finset.mem_univ j) (g_of_large hδ _ h)
  simp [H,hz]
end KirchbergRordam.GenericRW.CubeWeights
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_CubeField
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]

namespace KirchbergRordam.GenericRW.CubeField
open scoped BigOperators Topology
open Filter MatrixMix MatrixSimplex CubeWeights
variable {A : Type*} [CStarAlgebra A]
variable {n : ℕ} {φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A}
variable (F : Family φ)

lemma x_localized {δ : ℝ} (hδ : 0<δ) (t : Punctured n) (j : Fin (n+1))
    (hj : δ<(t.1 j:ℝ)) (hi : ∀ i,i≠j → (t.1 i:ℝ)<δ/2) (a b : Fin Size.n) :
    x F δ a b t.1=φ j (e a b) := by
  rw [x_apply,localized_normalized t hδ j hj hi,F.vertex,H_of_large hδ t.1 j hj.le,one_smul]
end KirchbergRordam.GenericRW.CubeField

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_AmplifiedComparison
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.ClosedRightRange
open scoped CStarAlgebra
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
omit instSize instPauliData in
lemma map_mem.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    {B : Type contextLevel2}
    [CStarAlgebra A]
    [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) {a z : A} (hz : z ∈ space a) :
    φ z ∈ space (φ a) := by
  have hh (z : space a) : φ (z : A) ∈ space (φ a) := by
    refine (dense a).induction_on z ((closed (φ a)).preimage ((map_continuous φ).comp continuous_subtype_val)) ?_
    intro x
    change φ (a*x) ∈ space (φ a)
    rw [map_mul]
    exact mem_space _ _
  exact hh ⟨z,hz⟩
end KirchbergRordam.GenericRW.ClosedRightRange

namespace KirchbergRordam.GenericRW.CuntzBelow
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


omit instSize instPauliData in
lemma of_right_range.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {b z : A} (hb : 0≤b) (hz : z ∈ ClosedRightRange.space b) :
    CuntzBelow (star z*z) b := by
  have hh (z : ClosedRightRange.space (CFC.sqrt b)) : CuntzBelow (star (z:A)*(z:A)) b := by
    refine (ClosedRightRange.dense (CFC.sqrt b)).induction_on z
      (isClosed_closure.preimage (by fun_prop)) ?_
    intro x
    apply of_eq (x:=x)
    change star x*b*x=star (CFC.sqrt b*x)*(CFC.sqrt b*x)
    rw [star_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq]
    calc
      _ = star x*(CFC.sqrt b*CFC.sqrt b)*x := by rw [CFC.sqrt_mul_sqrt_self b hb]
      _ = _ := by noncomm_ring
  rw [← Domination.sqrt_right_range_eq b hb] at hz
  exact hh ⟨z,hz⟩
end KirchbergRordam.GenericRW.CuntzBelow

namespace KirchbergRordam.GenericRW.AmplifiedComparison
open scoped CStarAlgebra
open scoped BigOperators
variable {P R B : Type*} [CStarAlgebra P] [CStarAlgebra R] [CStarAlgebra B]
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
variable (φ : P →⋆ₐ[ℂ] B) (ψ : R →⋆ₐ[ℂ] B)
variable (hc : ∀ a b, Commute (φ a) (ψ b))

omit instSize instPauliData in
lemma pair_zero_left.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (b : R) : pair φ ψ 0 b=0 := by simp [pair]
omit instSize instPauliData in
lemma pair_zero_right.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (a : P) : pair φ ψ a 0=0 := by simp [pair]
omit [DecidableEq I] in
omit instSize instPauliData in
lemma pair_sum_left.{contextLevel1, contextLevel2, contextLevel3, contextLevel4}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    {I : Type contextLevel4}
    [Fintype I]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (a : I→P) (b : R) : (∑ i,pair φ ψ (a i) b)=pair φ ψ (∑ i,a i) b := by
  simp only [pair,map_sum,Finset.sum_mul]
omit [DecidableEq J] in
omit instSize instPauliData in
lemma pair_sum_right.{contextLevel1, contextLevel2, contextLevel3, contextLevel4}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    {J : Type contextLevel4}
    [Fintype J]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (a : P) (b : J→R) : (∑ j,pair φ ψ a (b j))=pair φ ψ a (∑ j,b j) := by
  simp only [pair,map_sum,Finset.mul_sum]

variable [PartialOrder P] [StarOrderedRing P]
variable (y : J→P) (hy : ∀ j,0≤y j) (horth : ∀ j k,j≠k → y j*y k=0)
variable (u : J→I→P) (z : I→R) (v : J→R) (e : R)
variable (hz : ∀ i l,star (z i)*z l=if i=l then e else 0)

omit hy horth in
omit [Fintype J] [DecidableEq J] in
omit instSize instPauliData in
lemma sqrt_orthogonal.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    [CStarAlgebra P]
    {J : Type contextLevel2}
    [PartialOrder P]
    [StarOrderedRing P]
    (y : J → P)
    (hy : ∀ (j : J), 0 ≤ y j)
    (horth : ∀ (j k : J), j ≠ k → y j * y k = 0)
    (j k : J) (hjk : j≠k) : CFC.sqrt (y j)*CFC.sqrt (y k)=0 := by
  exact Intertwining.mul_sqrt_eq_zero (hy k) (Intertwining.sqrt_mul_eq_zero (hy j) (horth j k hjk))

include hc hy horth hz in
omit [Fintype I] [Fintype J] in
lemma gram_inner (j k : J) (i l : I) :
    star (gramVector φ ψ y u z v j i)*gramVector φ ψ y u z v k l =
      if j=k ∧ i=l then pair φ ψ (star (u j i)*y j*u j i) (star (v j)*e*v j) else 0 := by
  simp only [gramVector,pair_star φ ψ hc,pair_mul φ ψ hc,star_mul,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (y j))).star_eq]
  have hleft : (star (u j i)*CFC.sqrt (y j))*(CFC.sqrt (y k)*u k l)=
      star (u j i)*(CFC.sqrt (y j)*CFC.sqrt (y k))*u k l := by noncomm_ring
  have hright : (star (v j)*star (z i))*(z l*v k)=star (v j)*(star (z i)*z l)*v k := by noncomm_ring
  rw [hleft,hright,hz]
  by_cases hjk : j=k
  · subst k
    rw [CFC.sqrt_mul_sqrt_self (y j) (hy j)]
    by_cases hil : i=l
    · subst l; simp
    · simp [hil,pair_zero_right]
  · rw [sqrt_orthogonal y hy horth j k hjk]
    simp [hjk,pair_zero_left]

variable [PartialOrder B] [StarOrderedRing B]
include ψ hc hy horth z hz in


theorem compare (X : P)
    (hu : ∀ j,∑ i,star (u j i)*y j*u j i=X)
    (hv : ∑ j,star (v j)*e*v j=1) :
    CuntzBelow (φ X) (φ (∑ j,y j)) := by
  let w : B := ∑ j,∑ i,gramVector φ ψ y u z v j i
  have hww : star w*w=φ X := by
    dsimp only [w]
    simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
    simp_rw [gram_inner φ ψ hc y hy horth u z v e hz]
    simp only [ite_and]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp_rw [pair_sum_left,hu]
    rw [pair_sum_right,hv]
    simp [pair]
  have hY : 0≤∑ j,y j := Finset.sum_nonneg (fun j _ => hy j)
  have hw : w ∈ ClosedRightRange.space (φ (∑ j,y j)) := by
    apply (ClosedRightRange.space _).sum_mem
    intro j _
    apply (ClosedRightRange.space _).sum_mem
    intro i _
    apply ClosedRightRange.mul_right_mem
    apply ClosedRightRange.map_mem
    apply ClosedRightRange.mul_right_mem
    apply Domination.sqrt_mem_right_range (hy j) hY (by norm_num : (0:ℝ)≤1)
    simp only [one_smul]
    exact Finset.single_le_sum (fun k _ => hy k) (Finset.mem_univ j)
  rw [← hww]
  exact CuntzBelow.of_right_range (map_nonneg φ hY) hw
end KirchbergRordam.GenericRW.AmplifiedComparison
namespace KirchbergRordam.GenericRW.MaxTensor
open scoped BigOperators
universe u
variable {P Q : Type u} [CStarAlgebra P] [CStarAlgebra Q]

lemma word_mul (n : ℕ) (f g : Fin (n+1)→P) :
    word n f*word n g=word n (fun i => f i*g i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (pure_mul _ _ _ _).trans (congrArg (pure (f 0*g 0)) (ih _ _))
lemma word_star (n : ℕ) (f : Fin (n+1)→P) : star (word n f)=word n (fun i => star (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (pure_star _ _).trans (congrArg (pure (star (f 0))) (ih _))
lemma word_one (n : ℕ) : word n (fun _ => (1:P))=1 := by
  induction n with
  | zero => rfl
  | succ n ih => change pure 1 (word n fun _ => (1:P))=1; rw [ih,pure_one]
lemma word_zero_coordinate (n : ℕ) (f : Fin (n+1)→P) (i : Fin (n+1)) (hi : f i=0) : word n f=0 := by
  induction n with
  | zero =>
    have he : i=0 := by omega
    change f 0=0
    simpa only [he] using hi
  | succ n ih =>
    change pure (f 0) (word n (fun j => f j.succ))=0
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j,rfl⟩
    · rw [hi,pure_zero_left]
    · rw [ih _ j hi,pure_zero_right]

variable {I : Type*} [Fintype I]
lemma sum_word (n : ℕ) (f : I→P) :
    (∑ σ : Fin (n+1)→I,word n (fun i => f (σ i)))=word n (fun _ => ∑ a,f a) := by
  induction n with
  | zero =>
    exact (Equiv.funUnique (Fin 1) I).sum_comp f
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1+1) => I)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ a,∑ σ : Fin (n+1)→I,pure (f a) (word n (fun i => f (σ i))))=
      pure (∑ a,f a) (word n (fun _ => ∑ a,f a))
    simp_rw [← pure_sum_right,ih]
    rw [pure_sum_left]


lemma word_full_comparison (n : ℕ) (c : P) (v : I→P)
    (hv : ∑ i,star (v i)*c*v i=1) :
    ∑ σ : Fin (n+1)→I,star (word n (fun i => v (σ i)))*word n (fun _ => c)*
      word n (fun i => v (σ i))=1 := by
  simp_rw [word_star,word_mul]
  rw [sum_word n (fun i => star (v i)*c*v i),hv,word_one]

variable [DecidableEq I]
omit [Fintype I] in
lemma word_gram (n : ℕ) (c : P) (z : I→P)
    (hz : ∀ i j,star (z i)*z j=if i=j then c else 0)
    (σ τ : Fin (n+1)→I) :
    star (word n (fun i => z (σ i)))*word n (fun i => z (τ i))=
      if σ=τ then word n (fun _ => c) else 0 := by
  rw [word_star,word_mul]
  simp_rw [hz]
  by_cases h : σ=τ
  · subst τ; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact word_zero_coordinate n _ i (ite_eq_right hi)


theorem auxiliary {N : ℕ} (c : P) (v : Fin N→P)
    (hv : ∑ i,star (v i)*c*v i=1) (z : Fin 2→P)
    (hz : ∀ i j,star (z i)*z j=if i=j then c else 0) :
    ∃ L : ℕ, ∃ e : powerPack P L,
      ∃ a : Fin N→powerPack P L,
      ∃ b : (Fin (L+1)→Fin N)→powerPack P L,
        (∀ i j,star (a i)*a j=if i=j then e else 0) ∧
        (∑ j,star (b j)*e*b j=1) := by
  classical
  let L := Nat.log 2 N
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (Fin (L+1)→Fin 2) := by
    simp only [Fintype.card_fin,Fintype.card_fun]
    exact (Nat.lt_pow_succ_log_self (by norm_num : 1<2) N).le
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨L,word L (fun _ => c),fun i => word L (fun j => z (ι i j)),
    fun σ => word L (fun i => v (σ i)),?_,word_full_comparison L c v hv⟩
  intro i j
  rw [word_gram L c z hz]
  simp only [EmbeddingLike.apply_eq_iff_eq]
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra BigOperators ComplexOrder
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor ConeModel
omit instSize instPauliData in
lemma left_fixed
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) (a b : M2) (c : Fiber n) (hab : a*b=b) :
    MatrixTensor.leftMatrix a * (MatrixTensor.leftMatrix b * MatrixTensor.rightMatrix c)=
      MatrixTensor.leftMatrix b * MatrixTensor.rightMatrix c := by
  rw [← mul_assoc,← map_mul,hab]
lemma right_fixed (n : ℕ) (a : M2) (b c : Fiber n) (hbc : b*c=c) :
    MatrixTensor.rightMatrix b * (MatrixTensor.leftMatrix a * MatrixTensor.rightMatrix c)=
      MatrixTensor.leftMatrix a * MatrixTensor.rightMatrix c := by
  rw [← mul_assoc,← (MatrixTensor.legs_commute _ _).eq,mul_assoc,← map_mul,hbc]
lemma repr_word_succ (n : ℕ) (f : Fin (n+2) → ConeModel.Cone) (t : Cube (n+1)) :
    repr (n+1) (word (n+1) f) t=
      MatrixTensor.leftMatrix ((f 0:C(unitInterval,M2)) (t 0))*
        MatrixTensor.rightMatrix (repr n (word n (fun i=>f i.succ)) (tail n t)) := by
  have product_eq := congrArg (fun field : C(Cube (n+1),Fiber (n+1)) => field t)
    ((repr (n+1)).map_mul (includeLeft (f 0)) (includeRight (word n (fun i=>f i.succ))))
  exact product_eq.trans (congrArg₂ (· * ·) (repr_left n (f 0) t)
    (repr_right n (word n (fun i=>f i.succ)) t))

lemma repr_word_zero (n : ℕ) (f : Fin (n+1) → ConeModel.Cone) (t : Cube n) (j : Fin (n+1))
    (hj : (f j:C(unitInterval,M2)) (t j)=0) : repr n (word n f) t=0 := by
  induction n with
  | zero =>
    rw [Fin.eq_zero j] at hj
    exact hj
  | succ n ih =>
    have product_zero :
        MatrixTensor.leftMatrix (κ := PauliPower.Row n) ((f 0 : C(unitInterval,M2)) (t 0)) *
          MatrixTensor.rightMatrix (ι := Fin Size.n)
            (repr n (word n (fun index => f index.succ)) (tail n t)) = 0 := by
      induction j using Fin.cases with
      | zero => rw [hj,map_zero,zero_mul]
      | succ j => rw [ih _ (tail n t) j hj,map_zero,mul_zero]
    exact (repr_word_succ n f t).trans product_zero

lemma repr_word_fix (n : ℕ) (f : Fin (n+1) → ConeModel.Cone) (t : Cube n) (j : Fin (n+1)) (b : M2)
    (hj : b*(f j:C(unitInterval,M2)) (t j)=(f j:C(unitInterval,M2)) (t j)) :
    matLeg n j b*repr n (word n f) t=repr n (word n f) t := by
  induction n with
  | zero =>
    rw [Fin.eq_zero j] at hj
    exact hj
  | succ n ih =>
    simp only [repr_word_succ]
    induction j using Fin.cases with
    | zero => exact left_fixed n _ _ _ hj
    | succ j => exact right_fixed n _ _ _ (ih _ (tail n t) j hj)
end KirchbergRordam.GenericRW.ConeCube

namespace KirchbergRordam.GenericRW.ConeCut
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel MatrixMix
attribute [local instance] OAI.KirchbergRordam.GenericRW.ConeCut.instPartialOrderSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone
local instance instStarOrderedRingSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone : StarOrderedRing Cone := CStarAlgebra.spectralOrderedRing _

lemma unit_star (i j : Fin Size.n) : star (unit i j)=unit j i := by
  exact (map_star CStarMatrix.ofMatrixStarAlgEquiv (e i j)).symm.trans (congrArg CStarMatrix.ofMatrix (e_star i j))
lemma unit_mul (i j k l : Fin Size.n) : unit i j*unit k l=if j=k then unit i l else 0 := by
  change CStarMatrix.ofMatrixStarAlgEquiv (e i j)*CStarMatrix.ofMatrixStarAlgEquiv (e k l)=_
  rw [← map_mul,e_mul]
  split_ifs
  · rfl
  · exact map_zero CStarMatrix.ofMatrixStarAlgEquiv

omit instSize instPauliData in
lemma coeff_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) (t : unitInterval) : 0≤coeff δ t := le_max_right _ _

lemma z_gram (δ : ℝ) (hδ : 0≤δ) (i j : Fin Size.n) :
    star (z δ hδ i)*z δ hδ j=if i=j then q δ hδ else 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change star (Real.sqrt (coeff δ t) • unit i 0)*(Real.sqrt (coeff δ t) • unit j 0)=_
  rw [star_smul,star_trivial,unit_star,smul_mul_smul_comm,Real.mul_self_sqrt (coeff_nonneg δ t),unit_mul]
  split_ifs <;> simp [q]
attribute [local instance] OAI.KirchbergRordam.GenericRW.ConeCut.instLESubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone
lemma g_nonneg (δ : ℝ) : 0≤g δ := by
  let f : C(unitInterval,ℂ) := ⟨fun t => (CubeWeights.g δ t:ℂ),Complex.continuous_ofReal.comp (CubeWeights.g_continuous δ)⟩
  have hf : 0≤f := fun t => Complex.zero_le_real.mpr (CubeWeights.g_nonneg δ t)
  have he : star (scalar (CFC.sqrt f))*scalar (CFC.sqrt f)=g δ := by
    rw [← map_star,← map_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg f)).star_eq,
      CFC.sqrt_mul_sqrt_self f hf]
    rfl
  rw [← he]
  exact star_mul_self_nonneg _
lemma qg_zero {δ : ℝ} (hδ : 0<δ) : q δ hδ.le*g δ=0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (coeff δ t • unit 0 0)*(algebraMap ℂ M2 (↑(CubeWeights.g δ t)))=0
  by_cases ht : (t:ℝ)≤δ
  · rw [show coeff δ t=0 by simp [coeff,max_eq_right (sub_nonpos.mpr ht)],zero_smul,zero_mul]
  · rw [CubeWeights.g_of_large hδ t (le_of_not_ge ht),Complex.ofReal_zero,map_zero,mul_zero]
lemma q_support {δ : ℝ} (hδ : 0≤δ) (t : unitInterval)
    (hq : (q δ hδ:C(unitInterval,M2)) t≠0) : δ<(t:ℝ) := by
  by_contra ht
  apply hq
  change coeff δ t • unit 0 0=0
  rw [show coeff δ t=0 by simp [coeff,max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))],zero_smul]
lemma g_support {δ : ℝ} (hδ : 0<δ) (t : unitInterval)
    (hg : (g δ:C(unitInterval,M2)) t≠0) : (t:ℝ)<δ/2 := by
  apply CubeWeights.g_pos hδ
  apply lt_of_le_of_ne (CubeWeights.g_nonneg δ t)
  intro hz
  apply hg
  change algebraMap ℂ M2 (↑(CubeWeights.g δ t))=0
  rw [← hz,Complex.ofReal_zero,map_zero]
lemma q_fix (δ : ℝ) (hδ : 0≤δ) (t : unitInterval) :
    unit 0 0*(q δ hδ:C(unitInterval,M2)) t=(q δ hδ:C(unitInterval,M2)) t := by
  change unit 0 0*(coeff δ t • unit 0 0)=coeff δ t • unit 0 0
  rw [mul_smul_comm,unit_mul,ite_eq_left rfl]
end KirchbergRordam.GenericRW.ConeCut

namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

lemma x_fixes_y (n : ℕ) {δ : ℝ} (hδ : 0<δ) (j : Fin (n+1)) :
    x n δ 0 0*y n δ hδ.le j=y n δ hδ.le j := by
  apply faithful n
  rw [map_mul,repr_x]
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.mul_apply]
  by_cases hy : repr n (y n δ hδ.le j) t=0
  · rw [hy,mul_zero]
  · have hf (i : Fin (n+1)) :
        ((if i=j then ConeCut.q δ hδ.le else ConeCut.g δ : Cone) : C(unitInterval,M2)) (t i)≠0 := by
      intro hi
      exact hy (repr_word_zero n _ t i hi)
    have hj : δ<(t j:ℝ) := ConeCut.q_support hδ.le _ (by simpa using hf j)
    have hi (i : Fin (n+1)) (hij : i≠j) : (t i:ℝ)<δ/2 :=
      ConeCut.g_support hδ _ (by simpa [hij] using hf i)
    have ht : t≠0 := by
      intro hz
      have he : (t j:ℝ)=0 := by rw [hz]; rfl
      linarith
    rw [CubeField.x_localized (family n) hδ ⟨t,ht⟩ j hj hi]
    apply repr_word_fix n _ t j (ConeCut.unit 0 0)
    simpa only [ite_true] using ConeCut.q_fix δ hδ.le (t j)

omit instSize instPauliData in
lemma matrix_scalar_product
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) (a b : ℂ) :
    MatrixTensor.leftMatrix (κ:=PauliPower.Row n) (algebraMap ℂ M2 a) *
      MatrixTensor.rightMatrix (ι:=Fin Size.n) (algebraMap ℂ (Fiber n) b)=
        algebraMap ℂ (Fiber (n+1)) (a*b) := by
  rw [AlgHomClass.commutes,AlgHomClass.commutes,← map_mul]
  rfl

lemma repr_one (n : ℕ) : repr n (1:Tensor n)=1 :=
  (repr n).toAlgHom.map_one

lemma repr_scalar_word (n : ℕ) (f : Fin (n+1) → C(unitInterval,ℂ)) (t : Cube n) :
    repr n (word n (fun i => scalar (f i))) t = algebraMap ℂ (Fiber n) (∏ i,f i (t i)) := by
  induction n with
  | zero =>
    rw [Fin.prod_univ_succ]
    simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]
    rfl
  | succ n ih =>
    rw [repr_word_succ,ih]
    rw [scalar_apply]
    have product_eq := matrix_scalar_product n (f 0 (t 0))
      (∏ index : Fin (n+1), f index.succ (t index.succ))
    exact product_eq.trans (congrArg (algebraMap ℂ (Fiber (n+1)))
      (Fin.prod_univ_succ (fun i => f i (t i))).symm)

lemma defect_word (n : ℕ) (δ : ℝ) : 1-h n δ=word n (fun _=>ConeCut.g δ) := by
  apply faithful n
  rw [map_sub,repr_one,repr_h]
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.sub_apply]
  change 1-CubeWeights.H δ t • (1:Fiber n)=repr n (word n (fun _=>ConeCut.g δ)) t
  rw [ConeCut.g,repr_scalar_word]
  simp only [ContinuousMap.coe_mk,← Complex.ofReal_prod]
  rw [CubeWeights.H]
  rw [Algebra.algebraMap_eq_smul_one,Complex.coe_smul]
  module
end KirchbergRordam.GenericRW.ConeCube
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FullComparison
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.FullComparison
open scoped BigOperators WithCStarModule InnerProductSpace CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit instSize instPauliData in
lemma mem_span_list.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {c x : A} (hx : x ∈ TwoSidedIdeal.span {c}) :
    ∃ L : List (A × A), x = (L.map fun p => p.1 * c * p.2).sum := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    have he : x = c := hx
    subst x
    exact ⟨[(1,1)], by simp⟩
  | zero => exact ⟨[], by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨L,hL⟩ := ihx
    obtain ⟨M,hM⟩ := ihy
    exact ⟨L++M, by simp [hL,hM]⟩
  | neg x hx ih =>
    obtain ⟨L,hL⟩ := ih
    refine ⟨L.map fun p => (-p.1,p.2), ?_⟩
    simp only [List.map_map, Function.comp_def, neg_mul, hL]
    clear hL
    induction L with
    | nil => simp
    | cons p L ih => simpa [neg_add, add_comm] using congrArg (fun y => -(p.1*c*p.2)+y) ih
  | left_absorb a x hx ih =>
    obtain ⟨L,hL⟩ := ih
    refine ⟨L.map fun p => (a*p.1,p.2), ?_⟩
    simp only [List.map_map, Function.comp_def, mul_assoc, ← List.sum_map_mul_left, hL]
  | right_absorb a x hx ih =>
    obtain ⟨L,hL⟩ := ih
    refine ⟨L.map fun p => (p.1,p.2*a), ?_⟩
    simp only [List.map_map, Function.comp_def, ← mul_assoc, ← List.sum_map_mul_right, hL]

lemma finite_presentation {c : A} (hc : Fullness.IsFull c) :
    ∃ n : ℕ, ∃ h l : Fin n → A, ∑ i, h i*c*l i = 1 := by
  have hm : (1:A) ∈ TwoSidedIdeal.span {c} := by
    rw [show TwoSidedIdeal.span {c}=⊤ from hc]
    exact TwoSidedIdeal.mem_top A
  obtain ⟨L,hL⟩ := mem_span_list hm
  refine ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, ?_⟩
  have he := congrArg (fun M : List (A × A) => (M.map fun p => p.1*c*p.2).sum)
    (List.ofFn_get L)
  have hh : (∑ i, (L.get i).1*c*(L.get i).2) = (L.map fun p => p.1*c*p.2).sum := by
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def] using he
  exact hh.trans hL.symm


end KirchbergRordam.GenericRW.FullComparison

namespace KirchbergRordam.GenericRW.FullComparison
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
lemma exists_full_perturbation {b : A} (hfull : Fullness.IsFull b)
    (c : ℝ → A) (hn : ∀ δ,0≤δ → ‖b-c δ‖≤δ) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ Fullness.IsFull (c δ) := by
  classical
  obtain ⟨n,h,l,h1⟩ := finite_presentation hfull
  let K : ℝ := ∑ i, ‖h i‖*‖l i‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let δ : ℝ := 1/(2*(K+1))
  have hδ : 0 < δ := div_pos zero_lt_one (by positivity)
  have hδ1 : δ < 1 := by dsimp [δ]; apply (div_lt_one (by positivity)).mpr; linarith
  refine ⟨δ,hδ,hδ1,?_⟩
  let S := ∑ i, h i*c δ*l i
  have hnear : ‖1-S‖ < 1 := by
    have he : 1-S = ∑ i, h i*(b-c δ)*l i := by
      rw [← h1, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    have hnorm : ‖1-S‖ ≤ K*δ := by
      rw [he]
      apply (norm_sum_le _ _).trans
      calc
        ∑ i, ‖h i*(b-c δ)*l i‖ ≤ ∑ i, (‖h i‖*‖l i‖)*δ := by
          apply Finset.sum_le_sum
          intro i _
          calc
            _ ≤ (‖h i‖*‖b-c δ‖)*‖l i‖ := (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            _ ≤ (‖h i‖*δ)*‖l i‖ := by
              gcongr
              exact hn δ hδ.le
            _ = _ := by ring
        _ = _ := by rw [Finset.sum_mul]
    apply hnorm.trans_lt
    dsimp only [δ]
    rw [one_div, ← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hunit : IsUnit S := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnear
  have hmem : S ∈ TwoSidedIdeal.span {c δ} := by
    apply (TwoSidedIdeal.span {c δ}).asIdeal.sum_mem
    intro i _
    exact TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span rfl))
  apply TwoSidedIdeal.eq_top
  show (1:A) ∈ TwoSidedIdeal.span {c δ}
  obtain ⟨u,hu⟩ := hunit
  have hm := TwoSidedIdeal.mul_mem_left (TwoSidedIdeal.span {c δ}) (↑u⁻¹) S hmem
  simpa only [← hu, Units.inv_mul] using hm
end KirchbergRordam.GenericRW.FullComparison

namespace KirchbergRordam.GenericRW.FullComparison
open scoped BigOperators WithCStarModule InnerProductSpace CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


theorem full_comparison {c : A} (hc : 0 ≤ c) (hfull : Fullness.IsFull c) :
    ∃ n : ℕ, ∃ v : Fin n → A, ∑ i, star (v i)*c*v i = 1 := by
  classical
  obtain ⟨n,h,l,h1⟩ := finite_presentation hfull
  let X : C⋆ᵐᵒᵈ(A, Fin n → A) := (WithCStarModule.equiv A _).symm fun i => h i*CFC.sqrt c
  let Y : C⋆ᵐᵒᵈ(A, Fin n → A) := (WithCStarModule.equiv A _).symm fun i => star (l i)*CFC.sqrt c
  let d : A := ∑ i, star (l i)*c*l i
  have hs := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg c)).star_eq
  have hprod : inner A X Y = 1 := by
    simp only [X,Y,WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      WithCStarModule.inner_def, star_mul, hs]
    have hh : (∑ i, star (l i)*CFC.sqrt c*(CFC.sqrt c*star (h i))) =
        star (∑ i, h i*c*l i) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [star_mul, star_mul, (IsSelfAdjoint.of_nonneg hc).star_eq]
      calc
        _ = star (l i)*(CFC.sqrt c*CFC.sqrt c)*star (h i) := by noncomm_ring
        _ = _ := by rw [CFC.sqrt_mul_sqrt_self c hc]; noncomm_ring
    rw [hh,h1,star_one]
  have hYY : inner A Y Y = d := by
    simp only [Y,WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      WithCStarModule.inner_def, star_mul, hs, star_star]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = star (l i)*(CFC.sqrt c*CFC.sqrt c)*l i := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self c hc]
  have hdom : (1:A) ≤ ‖X‖^2 • d := by
    have hh := CStarModule.inner_mul_inner_swap_le (A := A) (x := X) (y := Y)
    rw [← CStarModule.star_inner X Y, hprod, star_one, one_mul, hYY] at hh
    exact hh
  have hd : IsStrictlyPositive (‖X‖^2 • d) := IsStrictlyPositive.of_le isStrictlyPositive_one hdom
  let r := (‖X‖^2 • d) ^ (-(1/2):ℝ)
  have hr : IsSelfAdjoint r := IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := ‖X‖^2 • d) (y := (-(1/2):ℝ)))
  refine ⟨n, fun i => ‖X‖ • (l i*r), ?_⟩
  calc
    ∑ i, star (‖X‖ • (l i*r))*c*(‖X‖ • (l i*r)) = r*(‖X‖^2 • d)*r := by
      simp only [star_smul, star_trivial, star_mul, hr.star_eq, smul_mul_assoc,
        mul_smul_comm, smul_smul]
      rw [← Finset.smul_sum, ← pow_two]
      congr 1
      dsimp only [d]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    _ = 1 := CFC.conjugate_rpow_neg_one_half _ hd
end KirchbergRordam.GenericRW.FullComparison

namespace KirchbergRordam.GenericRW.ConeCut
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel MatrixMix

lemma unit_norm (i j : Fin Size.n) : ‖unit i j‖≤1 :=
  CubeField.norm_matrix_unit CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom i j
omit instSize instPauliData in
lemma coeff_difference
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0≤δ) (t : unitInterval) : |coeff 0 t-coeff δ t|≤δ := by
  rw [coeff,sub_zero,max_eq_left t.2.1,coeff]
  apply abs_le.mpr
  constructor <;> by_cases h : (t:ℝ)-δ≤0
  · rw [max_eq_right h]; linarith [t.2.1]
  · rw [max_eq_left (le_of_not_ge h)]; linarith
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left (le_of_not_ge h)]; linarith
lemma norm_sub_q {δ : ℝ} (hδ : 0≤δ) : ‖q 0 (le_refl 0)-q δ hδ‖≤δ := by
  change ‖((q 0 (le_refl 0):Cone):C(unitInterval,M2))-(q δ hδ:C(unitInterval,M2))‖≤δ
  apply (ContinuousMap.norm_le _ hδ).mpr
  intro t
  change ‖coeff 0 t • unit 0 0-coeff δ t • unit 0 0‖≤δ
  rw [← sub_smul, ← IsScalarTower.algebraMap_smul ℂ, norm_smul,
    norm_algebraMap', Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (unit_norm 0 0)).trans (coeff_difference hδ t)

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
lemma exists_full_cut (η : Cone →⋆ₐ[ℂ] P) (hfull : Fullness.IsFull (η (q 0 (le_refl 0)))) :
    ∃ δ : ℝ, ∃ hδ : 0<δ, δ<1 ∧ Fullness.IsFull (η (q δ hδ.le)) := by
  let c : ℝ → P := fun δ => if hδ : 0≤δ then η (q δ hδ) else η (q 0 (le_refl 0))
  have hn (δ : ℝ) (hδ : 0≤δ) : ‖η (q 0 (le_refl 0))-c δ‖≤δ := by
    dsimp only [c]
    rw [dite_eq_left hδ,← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le η _).trans (norm_sub_q hδ)
  obtain ⟨δ,hδ,hδ1,hc⟩ := FullComparison.exists_full_perturbation hfull c hn
  exact ⟨δ,hδ,hδ1,by simpa [c,hδ.le] using hc⟩
end KirchbergRordam.GenericRW.ConeCut

namespace KirchbergRordam.GenericRW.MaxTensor
open scoped CStarAlgebra BigOperators
variable {P : Type*} [CStarAlgebra P]
variable {I : Type*} [Fintype I]
lemma word_sum_coordinate (n : ℕ) (j : Fin (n+1)) (a : I→P) (f : Fin (n+1)→P) :
    (∑ k,word n (fun i => if i=j then a k else f i))=
      word n (fun i => if i=j then ∑ k,a k else f i) := by
  induction n with
  | zero =>
    simp only [word,Fin.eq_zero j,ite_true]
    rfl
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      simp only [word,ite_true,Fin.succ_ne_zero,ite_false]
      exact (pure_sum_left a (word n (fun i => f i.succ))).symm
    | succ j =>
      have hj : (0 : Fin (n+2)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simp only [word,ite_eq_right hj,Fin.succ_inj]
      exact (pure_sum_right (f 0) (fun k => word n (fun i => if i=j then a k else f i.succ))).symm.trans
        (congrArg (pure (f 0)) (ih j (fun i => f i.succ)))

attribute [local instance] OAI.KirchbergRordam.GenericRW.MaxTensor.instPartialOrderCarrierPowerPack
local instance instStarOrderedRingCarrierPowerPack (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _
variable [PartialOrder P] [StarOrderedRing P]
lemma word_nonneg (n : ℕ) (f : Fin (n+1)→P) (hf : ∀ i,0≤f i) : 0≤word n f := by
  have he : star (word n (fun i=>CFC.sqrt (f i)))*word n (fun i=>CFC.sqrt (f i))=word n f := by
    rw [word_star,word_mul]
    congr 1
    funext i
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (f i))).star_eq,CFC.sqrt_mul_sqrt_self _ (hf i)]
  rw [← he]
  exact star_mul_self_nonneg _

lemma cornerWord_nonneg (n : ℕ) {c G : P} (hc : 0≤c) (hG : 0≤G) (j : Fin (n+1)) :
    0≤cornerWord n c G j := word_nonneg n _ (by intro i; split_ifs <;> assumption)
omit [PartialOrder P] [StarOrderedRing P] in
lemma cornerWord_orthogonal (n : ℕ) {c G : P} (hcG : c*G=0) (j k : Fin (n+1)) (hjk : j≠k) :
    cornerWord n c G j*cornerWord n c G k=0 := by
  rw [cornerWord,cornerWord,word_mul]
  apply word_zero_coordinate n _ j
  simp [hjk,hcG]
lemma columnWord_comparison (n : ℕ) {c G : P} (hG : 0≤G) (v : I→P)
    (hv : ∑ i,star (v i)*c*v i=1) (j : Fin (n+1)) :
    ∑ i,star (columnWord n G j (v i))*cornerWord n c G j*columnWord n G j (v i)=defectWord n G := by
  have he (i : I) : star (columnWord n G j (v i))*cornerWord n c G j*columnWord n G j (v i)=
      word n (fun k => if k=j then CFC.sqrt G*(star (v i)*c*v i)*CFC.sqrt G else G) := by
    simp only [columnWord,cornerWord,word_star,word_mul]
    congr 1
    funext k
    by_cases hk : k=j
    · simp only [ite_eq_left hk,star_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg G)).star_eq]
      noncomm_ring
    · simp [hk]
  simp_rw [he]
  rw [word_sum_coordinate]
  have hc : (∑ i,CFC.sqrt G*(star (v i)*c*v i)*CFC.sqrt G)=G := by
    rw [← Finset.sum_mul,← Finset.mul_sum,hv,mul_one,CFC.sqrt_mul_sqrt_self G hG]
  simp only [hc,ite_self,defectWord]
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.MaxTensor
universe u
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
omit instSize instPauliData in
lemma lift_pure
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {E F : Type u} {G : Type*} [CStarAlgebra E] [CStarAlgebra F] [CStarAlgebra G]
    (φ : E →⋆ₐ[ℂ] G) (ψ : F →⋆ₐ[ℂ] G) (hc : ∀ a b,Commute (φ a) (ψ b)) (a : E) (b : F) :
    lift φ ψ hc (pure a b)=φ a*ψ b := by
  have hl := DFunLike.congr_fun (lift_includeLeft φ ψ hc) a
  have hr := DFunLike.congr_fun (lift_includeRight φ ψ hc) b
  change lift φ ψ hc (includeLeft a)=φ a at hl
  change lift φ ψ hc (includeRight b)=ψ b at hr
  rw [pure,map_mul,hl,hr]
lemma powerHom_pure (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (a : A) (b : powerPack A n) :
    powerHom φ (n+1) (pure a b)=pure (φ a) (powerHom φ n b) := by
  exact lift_pure _ _ _ a b

lemma powerHom_word (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (f : Fin (n+1)→A) :
    powerHom φ n (word n f)=word n (fun i=>φ (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih => change powerHom φ (n+1) (pure (f 0) (word n _))=_; rw [powerHom_pure,ih]; rfl
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize instPauliData in
lemma support_cut_cfc.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) (δ : ℝ) :
    ExactCut.cut a δ = cfc (fun t : ℝ => max (t-δ) 0) a := by
  rw [ExactCut.cut, CFC.posPart_def, cfcₙ_eq_cfc]
  have hd : cfc (fun t : ℝ => t-δ) a = a-algebraMap ℝ A δ := by
    rw [cfc_sub ..]
    change cfc id a - cfc (fun _ : ℝ => δ) a = _
    rw [cfc_id ℝ a ha, cfc_const _ _ ha]
  rw [← hd, ← cfc_comp (fun t : ℝ => t⁺) (fun t : ℝ => t-δ) a ha]
  rfl

omit [Nontrivial A] in
lemma support_cut_comparison {a Y : A} (ha : IsSelfAdjoint a) (hY : 0≤Y) (hfix : a*Y=Y) :
    CuntzBelow Y (ExactCut.cut a (1/2)) := by
  have hz : (a-1)*Y=0 := by rw [sub_mul,hfix,one_mul,sub_self]
  have hsz := Intertwining.mul_sqrt_eq_zero hY hz
  have has : a*CFC.sqrt Y=CFC.sqrt Y := by
    simpa only [sub_mul,one_mul,sub_eq_zero] using hsz
  have hs : CFC.sqrt Y*1=a*CFC.sqrt Y := by simpa only [mul_one] using has.symm
  have hc := Intertwining.cfc (A:=A) (v:=CFC.sqrt Y) (a:=1) (b:=a)
    (IsSelfAdjoint.one A) ha hs (fun t : ℝ => max (t-1/2) 0) (by fun_prop)
  rw [← support_cut_cfc ha (1/2)] at hc
  have hone : cfc (fun t : ℝ => max (t-1/2) 0) (1:A)=(1/2:ℝ) • (1:A) := by
    rw [cfc_apply_one,Algebra.algebraMap_eq_smul_one]
    norm_num
  rw [hone,mul_smul_comm,mul_one] at hc
  let v : A := Real.sqrt 2 • CFC.sqrt Y
  have hv : star v*ExactCut.cut a (1/2)*v=Y := by
    dsimp only [v]
    rw [star_smul,star_trivial,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)).star_eq,
      smul_mul_assoc,smul_mul_smul_comm,Real.mul_self_sqrt (by norm_num),mul_assoc,← hc,mul_smul_comm,
      CFC.sqrt_mul_sqrt_self Y hY,smul_smul]
    norm_num
  exact CuntzBelow.of_eq hv
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FiniteDrop
attribute [-instance] _root_.OAI.KirchbergRordam.MaxTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.StarCompletion.completionNormedStarGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.ConeDrop
open scoped CStarAlgebra ComplexOrder BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor ConeModel
attribute [local instance] OAI.KirchbergRordam.GenericRW.ConeDrop.instPartialOrderSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone
local instance instStarOrderedRingSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone : StarOrderedRing Cone := CStarAlgebra.spectralOrderedRing _
variable {P : Type*} [CStarAlgebra P]
attribute [local instance] OAI.KirchbergRordam.GenericRW.ConeDrop.instPartialOrderCarrierPowerPack
local instance instStarOrderedRingCarrierPowerPack (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _

lemma map_y (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) (δ : ℝ) (hδ : 0≤δ) (j : Fin (k+1)) :
    powerHom η k (ConeCube.y k δ hδ j)=cornerWord k (η (ConeCut.q δ hδ)) (η (ConeCut.g δ)) j := by
  rw [ConeCube.y,powerHom_word,cornerWord]
  congr 1
  funext i
  split_ifs <;> rfl
lemma map_defect (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) (δ : ℝ) :
    1-powerHom η k (ConeCube.h k δ)=defectWord k (η (ConeCut.g δ)) := by
  rw [← map_one (powerHom η k),← map_sub,ConeCube.defect_word,powerHom_word]
  rfl
lemma map_fix (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) {δ : ℝ} (hδ : 0<δ) (j : Fin (k+1)) :
    powerHom η k (ConeCube.x k δ 0 0)*cornerWord k (η (ConeCut.q δ hδ.le)) (η (ConeCut.g δ)) j=
      cornerWord k (η (ConeCut.q δ hδ.le)) (η (ConeCut.g δ)) j := by
  rw [← map_y,← map_mul,ConeCube.x_fixes_y k hδ j]

omit instSize instPauliData in
lemma map_nonneg_generic
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    [pE : PartialOrder E] [StarOrderedRing E] [PartialOrder F] [StarOrderedRing F]
    (φ : E →⋆ₐ[ℂ] F) {a : E} (ha : 0≤a) : 0≤φ a := map_nonneg φ ha
variable [Nontrivial P] [PartialOrder P] [StarOrderedRing P]


theorem exists_drop_from_full_cone (η : Cone →⋆ₐ[ℂ] P)
    (hfull : Fullness.IsFull (η (ConeCut.q 0 (le_refl 0)))) :
    ∃ m : ℕ, Nonempty (DimensionDrop23 →⋆ₐ[ℂ] powerPack P m) := by
  classical
  obtain ⟨δ,hδ,hδ1,hfullδ⟩ := ConeCut.exists_full_cut η hfull
  let c := η (ConeCut.q δ hδ.le)
  let G := η (ConeCut.g δ)
  let z : Fin 2→P := fun i=>η (ConeCut.z δ hδ.le (Fin.castLE PauliData.two_le i))
  have hz (i j : Fin 2) : star (z i)*z j=if i=j then c else 0 := by
    dsimp only [z,c]
    rw [← map_star,← map_mul,ConeCut.z_gram]
    have he : (Fin.castLE PauliData.two_le i = Fin.castLE PauliData.two_le j) ↔ i=j :=
      (Fin.castLE_injective PauliData.two_le).eq_iff
    simp only [he, apply_ite, map_zero]
    split_ifs <;> rfl
  have hc : 0≤c := by rw [← show star (z 0)*z 0=c by simpa using hz 0 0]; exact star_mul_self_nonneg _
  have hG : 0≤G := map_nonneg_generic (pE:=CStarAlgebra.spectralOrder Cone) η (ConeCut.g_nonneg δ)
  have hcG : c*G=0 := by dsimp only [c,G]; rw [← map_mul,ConeCut.qg_zero hδ,map_zero]
  obtain ⟨N,v,hv⟩ := FullComparison.full_comparison hc hfullδ
  have hN : N≠0 := by intro he; subst N; simp at hv
  let : NeZero N := ⟨hN⟩
  obtain ⟨L,e,a,b,ha,hb⟩ := auxiliary c v hv z hz
  let J := Fin (L+1)→Fin N
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α:=J))
  let σ : Fin (k+1)≃J := (Fintype.equivFinOfCardEq hk).symm
  let Y : Fin (k+1)→powerPack P k := cornerWord k c G
  let U : Fin (k+1)→Fin N→powerPack P k := fun j i=>columnWord k G j (v i)
  let V : Fin (k+1)→powerPack P L := fun j=>b (σ j)
  have hV : ∑ j,star (V j)*e*V j=1 := by
    have he := σ.sum_comp (fun j=>star (b j)*e*b j)
    exact he.trans hb
  let B := MaxTensor.Algebra (powerPack P k) (powerPack P L)
  let : PartialOrder B := CStarAlgebra.spectralOrder _
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
  let φ : powerPack P k →⋆ₐ[ℂ] B := includeLeft
  let ψ : powerPack P L →⋆ₐ[ℂ] B := includeRight
  let W := ((ConeCube.weighted k hδ).map (powerHom η k)).map φ
  have hY (j) : 0≤Y j := cornerWord_nonneg k hc hG j
  have hYY (j l) (hjl : j≠l) : Y j*Y l=0 := cornerWord_orthogonal k hcG j l hjl
  have hU (j) : ∑ i,star (U j i)*Y j*U j i=defectWord k G := columnWord_comparison k hG v hv j
  have hcomp := AmplifiedComparison.compare φ ψ (fun x y=>legs_commute x y)
    Y hY hYY U a V e ha (defectWord k G) hU hV
  have hsum : 0≤φ (∑ j,Y j) := map_nonneg φ (Finset.sum_nonneg (fun j _=>hY j))
  have hfix : W.x 0 0*φ (∑ j,Y j)=φ (∑ j,Y j) := by
    change φ (powerHom η k (ConeCube.x k δ 0 0))*φ (∑ j,Y j)=_
    rw [← map_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact map_fix η k hδ j
  have hcut := support_cut_comparison (W.star_x 0 0) hsum hfix
  have hdef : 1-W.h=φ (defectWord k G) := by
    change 1-φ (powerHom η k (ConeCube.h k δ))=_
    rw [← map_one φ,← map_sub,map_defect]
  have hw : CuntzBelow (1-W.h) (ExactCut.cut (W.x 0 0) (1/2)) := by
    rw [hdef]
    exact hcomp.trans hcut
  obtain ⟨flatten⟩ := exists_joinPower P k L
  exact ⟨k+L+1,⟨flatten.comp (W.cutoffHom hw)⟩⟩
end KirchbergRordam.GenericRW.ConeDrop

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [instNontrivialA : Nontrivial A]
omit instSize instPauliData instNontrivialA in
lemma pure_full
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type u}
    {B : Type u}
    [CStarAlgebra A]
    [CStarAlgebra B]
    [PartialOrder A]
    [StarOrderedRing A]
    [PartialOrder B]
    [StarOrderedRing B]
    [Nontrivial A]
    {a : A} {b : B} (ha : IsFull a) (hb : IsFull b) : IsFull (pure a b) := by
  classical
  obtain ⟨n,h,l,h1⟩ := FullComparison.finite_presentation ha
  obtain ⟨m,s,t,h2⟩ := FullComparison.finite_presentation hb
  let K := TwoSidedIdeal.span ({pure a b} : Set (Algebra A B))
  apply TwoSidedIdeal.eq_top
  have he : (∑ i : Fin n, ∑ j : Fin m, pure (h i) (s j)*pure a b*pure (l i) (t j))=1 := by
    simp only [pure_mul]
    simp_rw [← pure_sum_right]
    rw [← pure_sum_left,h1,h2,pure_one]
  rw [← he]
  apply K.asIdeal.sum_mem
  intro i hi
  apply K.asIdeal.sum_mem
  intro j hj
  exact K.mul_mem_right _ _ (K.mul_mem_left _ _ (TwoSidedIdeal.subset_span (by simp)))
end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {P : Type u} [CStarAlgebra P]

variable [Nontrivial P]
attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instPartialOrderCarrierPowerPack
attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instStarOrderedRingCarrierPowerPack
attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instPartialOrder_solutions
attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instStarOrderedRing_solutions
lemma power_full (W : WeightedUnits (Fin 2) P) (hW : ∀ i, IsFull (W.x i i))
    (k : ℕ) (i : Row k) : IsFull ((power W k).x i i) := by
  induction k with
  | zero => exact hW i
  | succ k ih => exact pure_full (hW i.1) (ih i.2)

omit instSize instPauliData in
lemma exists_flatten
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (D : Type u) [CStarAlgebra D] (n k : ℕ) :
    ∃ m : ℕ, Nonempty (powerPack (powerPack D n) k →⋆ₐ[ℂ] powerPack D m) := by
  induction k with
  | zero => exact ⟨n,⟨StarAlgHom.id ℂ _⟩⟩
  | succ k ih =>
    obtain ⟨m,⟨φ⟩⟩ := ih
    obtain ⟨ψ⟩ := exists_joinPower D n m
    exact ⟨n+m+1,⟨ψ.comp (MaxTensor.map (StarAlgHom.id ℂ (powerPack D n)) φ)⟩⟩
end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
section
open OrderZero Fullness _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [instNontrivialA : Nontrivial A]
omit instSize instPauliData in
lemma sqrt_star_mul_self_full.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    [instNontrivialA : Nontrivial A]
    {w : A} (hw : IsFull w) : IsFull (CFC.sqrt (star w*w)) := by
  apply full_of_survives
  intro π he
  have hh := congrArg π.representation (CFC.sqrt_mul_sqrt_self (star w*w))
  rw [map_mul,he,zero_mul,map_mul,map_star] at hh
  exact full_survives hw π.representation ((CStarRing.star_mul_self_eq_zero_iff _).mp hh.symm)
omit instSize instPauliData in
lemma sqrt_mul_star_self_full.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    [instNontrivialA : Nontrivial A]
    {w : A} (hw : IsFull w) : IsFull (CFC.sqrt (w*star w)) := by
  apply full_of_survives
  intro π he
  have hh := congrArg π.representation (CFC.sqrt_mul_sqrt_self (w*star w))
  rw [map_mul,he,zero_mul,map_mul,map_star] at hh
  exact full_survives hw π.representation ((CStarRing.mul_star_self_eq_zero_iff _).mp hh.symm)

lemma ofSquareZero_full {w : A} (hw : w*w=0) (hn : ‖w‖≤1) (hf : IsFull w) (i : Fin 2) :
    IsFull ((ofSquareZero hw hn).x i i) := by
  fin_cases i
  · exact sqrt_star_mul_self_full hf
  · exact sqrt_mul_star_self_full hf
end

open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]
omit [Size] [PauliData] in
theorem exists_full_cone (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    ∃ m : ℕ, ∃ η : @ConeModel.Cone (powerSize k) →⋆ₐ[ℂ] powerPack D m,
      IsFull (η (@ConeModel.corner (powerSize k) 0 0)) := by
  let : Size := powerSize k
  let : PauliData := powerPauliData k
  obtain ⟨n,y,hyz,hyfull⟩ := FullSquareZero.exists_full_square_zero hD
  obtain ⟨w,hwz,hwfull,hwn⟩ := FullSquareZero.normalize hyz hyfull
  let := CStarAlgebra.spectralOrder (powerPack D n)
  let := CStarAlgebra.spectralOrderedRing (powerPack D n)
  let W := ofSquareZero hwz hwn.le
  let := CStarAlgebra.spectralOrder (powerPack (powerPack D n) k)
  let := CStarAlgebra.spectralOrderedRing (powerPack (powerPack D n) k)
  let V := reindex (power W k) (rowEquiv k)
  obtain ⟨m,⟨φ⟩⟩ := exists_flatten D n k
  let := CStarAlgebra.spectralOrder (powerPack D m)
  let := CStarAlgebra.spectralOrderedRing (powerPack D m)
  let R := V.map φ
  refine ⟨m,R.coneHom,?_⟩
  rw [R.coneHom_corner]
  apply Fullness.full_map
  exact power_full W (ofSquareZero_full hwz hwn.le hwfull) k ((rowEquiv k).symm 0)
end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.ConeCut
lemma q_zero_eq_corner : q 0 (le_refl 0)=ConeModel.corner 0 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [ConeModel.corner_apply]
  change coeff 0 t • unit 0 0=(↑(t:ℝ):ℂ) • CStarMatrix.ofMatrix (Matrix.single 0 0 1)
  rw [show coeff 0 t=(t:ℝ) by simp [coeff,max_eq_left t.property.1]]
  exact (Complex.coe_smul _ _).symm
end KirchbergRordam.GenericRW.ConeCut

namespace KirchbergRordam.GenericRW
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
omit [Size] [PauliData] in


theorem finite_prime_power_drop (D : Type*) [CStarAlgebra D] [Nontrivial D]
    (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    ∃ m : ℕ, Nonempty (@DimensionDrop23 (powerSize k) →⋆ₐ[ℂ] powerPack D m) := by
  let : Size := powerSize k
  let : PauliData := powerPauliData k
  obtain ⟨n,η,hη⟩ := FullRankWeighted.exists_full_cone hD k
  let := CStarAlgebra.spectralOrder (powerPack D n)
  let := CStarAlgebra.spectralOrderedRing (powerPack D n)
  obtain ⟨l,⟨φ⟩⟩ := ConeDrop.exists_drop_from_full_cone η (by rwa [ConeCut.q_zero_eq_corner])
  obtain ⟨m,⟨ψ⟩⟩ := FullRankWeighted.exists_flatten D n l
  exact ⟨m,⟨ψ.comp φ⟩⟩
end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_NormUltrapower
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]


open Filter Topology BoundedContinuousFunction

universe uQuot

namespace KirchbergRordam
namespace NormUltrapower

variable {A : Type*} [CStarAlgebra A]


theorem normLimit_nonneg (ω : Ultrafilter ℕ) (x : BoundedSeq A) : 0 ≤ normLimit ω x :=
  (exists_norm_limit ω x).choose_spec.1.1

theorem normLimit_le (ω : Ultrafilter ℕ) (x : BoundedSeq A) : normLimit ω x ≤ ‖x‖ :=
  (exists_norm_limit ω x).choose_spec.1.2

theorem normLimit_add_le (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    normLimit ω (x + y) ≤ normLimit ω x + normLimit ω y := by
  exact le_of_tendsto_of_tendsto (tendsto_norm ω (x+y))
    ((tendsto_norm ω x).add (tendsto_norm ω y))
    (Eventually.of_forall fun n => norm_add_le (x n) (y n))

theorem normLimit_sub_le (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    normLimit ω x - normLimit ω y ≤ normLimit ω (x-y) := by
  have h := normLimit_add_le ω (x-y) y
  rw [sub_add_cancel] at h
  linarith


theorem normLimit_eq_of_sub_mem (ω : Ultrafilter ℕ) {x y : BoundedSeq A}
    (h : x-y ∈ nullIdeal ω) : normLimit ω x = normLimit ω y := by
  change normLimit ω (x-y) = 0 at h
  apply le_antisymm
  · have h' := normLimit_sub_le ω x y
    linarith
  · have h' := normLimit_sub_le ω y x
    rw [← neg_sub x y, normLimit_neg, h] at h'
    linarith


theorem normLimit_le_quotient (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω x ≤ ‖Ideal.Quotient.mk (nullIdeal ω) x‖ := by
  apply QuotientAddGroup.le_norm_iff.mpr
  intro y hy
  have h : y-x ∈ nullIdeal ω := (Ideal.Quotient.eq).mp hy
  rw [← normLimit_eq_of_sub_mem ω h]
  exact normLimit_le ω y


theorem cutRepresentative_norm_le (x : BoundedSeq A) (c : ℝ) (hc : 0 ≤ c) :
    ‖cutRepresentative x c hc‖ ≤ c := by
  apply (BoundedContinuousFunction.norm_le hc).mpr
  intro n
  change ‖if ‖x n‖ < c then x n else 0‖ ≤ c
  split_ifs with h
  · exact h.le
  · simpa only [norm_zero] using hc

theorem cutRepresentative_mk_eq (ω : Ultrafilter ℕ) (x : BoundedSeq A)
    (c : ℝ) (hc : 0 ≤ c) (hlim : normLimit ω x < c) :
    Ideal.Quotient.mk (nullIdeal ω) x =
      Ideal.Quotient.mk (nullIdeal ω) (cutRepresentative x c hc) := by
  rw [Ideal.Quotient.eq, mem_nullIdeal]
  have he : ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ < c :=
    (tendsto_norm ω x).eventually (eventually_lt_nhds hlim)
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0) := tendsto_const_nhds
  apply hz.congr'
  filter_upwards [he] with n hn
  change (0 : ℝ) = ‖x n - (if ‖x n‖ < c then x n else 0)‖
  rw [ite_eq_left hn, sub_self, norm_zero]


theorem quotient_norm_le_normLimit (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ‖Ideal.Quotient.mk (nullIdeal ω) x‖ ≤ normLimit ω x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos : 0 ≤ normLimit ω x + ε := add_nonneg (normLimit_nonneg ω x) hε.le
  rw [cutRepresentative_mk_eq ω x (normLimit ω x + ε) hpos (lt_add_of_pos_right _ hε)]
  have hb := Submodule.Quotient.norm_mk_le (nullIdeal ω)
    (cutRepresentative x (normLimit ω x + ε) hpos)
  exact hb.trans (cutRepresentative_norm_le x (normLimit ω x + ε) hpos)


theorem norm_mk_eq (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ‖Ideal.Quotient.mk (nullIdeal ω) x‖ = normLimit ω x :=
  le_antisymm (quotient_norm_le_normLimit ω x) (normLimit_le_quotient ω x)


theorem normLimit_const (ω : Ultrafilter ℕ) (a : A) :
    normLimit ω (constantSeq a) = ‖a‖ :=
  tendsto_nhds_unique (tendsto_norm ω (constantSeq a)) tendsto_const_nhds

@[simp]
theorem norm_diagonal (ω : Ultrafilter ℕ) (a : A) : ‖diagonal ω a‖ = ‖a‖ := by
  change ‖Ideal.Quotient.mk (nullIdeal ω) (constantSeq a)‖ = ‖a‖
  rw [norm_mk_eq, normLimit_const]

theorem diagonal_isometry (ω : Ultrafilter ℕ) : Isometry (diagonal (A := A) ω) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_eq_norm, ← map_sub, norm_diagonal, dist_eq_norm]

instance quotientNontrivial (ω : Ultrafilter ℕ) [Nontrivial A] : Nontrivial (Algebra A ω) :=
  (diagonal_isometry ω).injective.nontrivial


instance centralNontrivial (ω : Ultrafilter ℕ) [Nontrivial A] :
    Nontrivial (CentralAlgebra A ω) := inferInstance

theorem mem_central_iff (ω : Ultrafilter ℕ) (z : Algebra A ω) :
    z ∈ centralSubalgebra ω ↔ ∀ a : A, diagonal ω a * z = z * diagonal ω a := by
  change z ∈ StarSubalgebra.centralizer ℂ (Set.range (diagonal ω)) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h (diagonal ω a) ⟨a, rfl⟩).1
  · intro h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨h a, by simpa only [map_star] using h (star a)⟩


theorem mk_mem_central_iff (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    quotientMap ω x ∈ centralSubalgebra ω ↔
      ∀ a : A, Tendsto (fun n => ‖x n * a - a * x n‖) (ω : Filter ℕ) (𝓝 0) := by
  rw [mem_central_iff]
  constructor
  · intro h a
    have he : Ideal.Quotient.mk (nullIdeal ω) (x * constantSeq a) =
        Ideal.Quotient.mk (nullIdeal ω) (constantSeq a * x) := (h a).symm
    exact (mem_nullIdeal ω _).mp (Ideal.Quotient.eq.mp he)
  · intro h a
    have he : x * constantSeq a - constantSeq a * x ∈ nullIdeal ω :=
      (mem_nullIdeal ω _).mpr (h a)
    exact (Ideal.Quotient.eq.mpr he).symm

end NormUltrapower
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Reindexing
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction

open Filter Topology
namespace KirchbergRordam.Reindex


theorem diagonal_select {ι : Type*} [Countable ι] (ω : Filter ℕ) [NeBot ω]
    (f : ι → ℕ → ℕ → ℝ)
    (hf : ∀ i s, Tendsto (f i s) ω (𝓝 0)) :
    ∃ k : ℕ → ℕ, ∀ i, Tendsto (fun s => f i s (k s)) atTop (𝓝 0) := by
  classical
  let := Encodable.ofCountable ι
  have good (s : ℕ) : ∃ l, ∀ i, Encodable.encode i ≤ s → |f i s l| < 1 / ((s:ℝ)+1) := by
    have hfin : {i : ι | Encodable.encode i ≤ s}.Finite :=
      (Set.finite_Iic s).preimage Encodable.encode_injective.injOn
    have he : ∀ᶠ l in ω, ∀ i ∈ {i : ι | Encodable.encode i ≤ s},
        |f i s l| < 1 / ((s:ℝ)+1) := hfin.eventually_all.mpr fun i _ => by
      have hp : (0:ℝ) < 1 / ((s:ℝ)+1) := by positivity
      simpa only [Real.dist_eq, sub_zero] using
        (tendsto_order.1 ((hf i s).abs)).2 _ (by simpa using hp)
    exact he.exists
  choose k hk using good
  refine ⟨k, fun i => ?_⟩
  apply squeeze_zero_norm' (a := fun s : ℕ => 1 / ((s:ℝ)+1))
  · filter_upwards [eventually_ge_atTop (Encodable.encode i)] with s hs
    simpa only [Real.norm_eq_abs] using (hk s i hs).le
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
end KirchbergRordam.Reindex

namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]


theorem countable_reindex {S : Type*} [Ring S] [StarRing S] [Countable S]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : S →+* Algebra A ω) (hφ : ∀ x, φ (star x) = star (φ x))
    (hc : ∀ x, φ x ∈ centralSubalgebra ω)
    (j : S) (hj : φ j = diagonal ω (algebraMap ℂ A Complex.I))
    (b : ℕ → BoundedSeq A) :
    ∃ θ : S →+* CentralAlgebra A ω,
      (∀ x, θ (star x) = star (θ x)) ∧
      (∀ x, ‖θ x‖ = ‖φ x‖) ∧
      (θ j : Algebra A ω) = diagonal ω (algebraMap ℂ A Complex.I) ∧
      ∀ x n, Commute (θ x : Algebra A ω) (quotientMap ω (b n)) := by
  classical
  have hex (x : S) : ∃ u : BoundedSeq A, quotientMap ω u = φ x :=
    Ideal.Quotient.mk_surjective _
  choose u hu using hex
  let a : ℕ → A := TopologicalSpace.denseSeq A
  have ha : DenseRange a := TopologicalSpace.denseRange_denseSeq A
  let test : ReindexTest S → ℕ → ℕ → ℝ
    | .add x y, _, l => ‖u (x+y) l - (u x l + u y l)‖
    | .mul x y, _, l => ‖u (x*y) l - u x l * u y l‖
    | .adjoint x, _, l => ‖u (star x) l - star (u x l)‖
    | .zero, _, l => ‖u 0 l - 0‖
    | .one, _, l => ‖u 1 l - 1‖
    | .norm x, _, l => ‖u x l‖ - ‖φ x‖
    | .central x n, _, l => ‖u x l * a n - a n * u x l‖
    | .commute x n, s, l => ‖u x l * b n s - b n s * u x l‖
    | .imag, _, l => ‖u j l - algebraMap ℂ A Complex.I‖
  have ht (i : ReindexTest S) (s : ℕ) : Tendsto (test i s) (ω : Filter ℕ) (𝓝 0) := by
    have hn (x y : BoundedSeq A) (h : quotientMap ω x = quotientMap ω y) :=
      (quotient_eq_iff ω x y).mp h
    have hcent x : ∀ c : A, Tendsto (fun l => ‖u x l * c - c * u x l‖)
        (ω : Filter ℕ) (𝓝 0) := (mk_mem_central_iff ω (u x)).mp (by rw [hu]; exact hc x)
    cases i with
    | add x y => exact hn (u (x+y)) (u x + u y) (by simp only [hu, map_add])
    | mul x y => exact hn (u (x*y)) (u x * u y) (by simp only [hu, map_mul])
    | adjoint x => exact hn (u (star x)) (star (u x)) (by simp only [hu, map_star, hφ])
    | zero => exact hn (u 0) 0 (by simp only [hu, map_zero])
    | one => exact hn (u 1) 1 (by simp only [hu, map_one])
    | norm x =>
      have he : normLimit ω (u x) = ‖φ x‖ := by rw [← hu]; exact (norm_mk_eq ω (u x)).symm
      simpa only [he, sub_self] using (tendsto_norm ω (u x)).sub_const ‖φ x‖
    | central x n => exact hcent x (a n)
    | commute x n => exact hcent x (b n s)
    | imag => exact hn (u j) (constantSeq (algebraMap ℂ A Complex.I)) (by rw [hu,hj]; rfl)
  obtain ⟨k,hk⟩ := Reindex.diagonal_select (ω : Filter ℕ) test ht
  have hfree : (ω : Filter ℕ) ≤ atTop := by simpa only [Nat.cofinite_eq_atTop] using hω
  have hk' (i : ReindexTest S) : Tendsto (fun s => test i s (k s)) (ω : Filter ℕ) (𝓝 0) :=
    (hk i).mono_left hfree
  let v : S → BoundedSeq A := fun x => reindexed k (u x)
  let g : S → Algebra A ω := fun x => quotientMap ω (v x)
  have heq (x y : BoundedSeq A)
      (h : Tendsto (fun s => ‖x s - y s‖) (ω : Filter ℕ) (𝓝 0)) :
      quotientMap ω x = quotientMap ω y := (quotient_eq_iff ω x y).mpr h
  have hadd (x y : S) : g (x+y) = g x + g y := by
    change quotientMap ω (v (x+y)) = _
    rw [← map_add]
    exact heq _ _ (hk' (.add x y))
  have hmul (x y : S) : g (x*y) = g x * g y := by
    change quotientMap ω (v (x*y)) = _
    rw [← map_mul]
    exact heq _ _ (hk' (.mul x y))
  have hstar (x : S) : g (star x) = star (g x) := by
    change quotientMap ω (v (star x)) = _
    rw [← map_star]
    exact heq _ _ (hk' (.adjoint x))
  have hzero : g 0 = 0 := by
    rw [← map_zero (quotientMap ω)]
    exact heq _ _ (hk' .zero)
  have hone : g 1 = 1 := by
    rw [← map_one (quotientMap ω)]
    exact heq _ _ (hk' .one)
  have hgNorm (x : S) : ‖g x‖ = ‖φ x‖ := by
    change ‖quotientMap ω (v x)‖ = _
    change ‖Ideal.Quotient.mk (nullIdeal ω) (v x)‖ = _
    rw [norm_mk_eq]
    apply tendsto_nhds_unique (tendsto_norm ω (v x))
    simpa only [test, v, reindexed_apply, sub_add_cancel, zero_add] using (hk' (.norm x)).add_const ‖φ x‖
  have hgCentral (x : S) : g x ∈ centralSubalgebra ω := by
    rw [mem_central_iff]
    intro c
    refine ha.induction_on c (p := fun c => diagonal ω c * g x = g x * diagonal ω c)
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro n
    have he := heq (v x * constantSeq (a n)) (constantSeq (a n) * v x) (hk' (.central x n))
    change quotientMap ω (constantSeq (a n)) * quotientMap ω (v x) =
      quotientMap ω (v x) * quotientMap ω (constantSeq (a n))
    simpa only [map_mul] using he.symm
  let θ : S →+* CentralAlgebra A ω :=
    { toFun := fun x => ⟨g x, hgCentral x⟩
      map_zero' := Subtype.ext hzero
      map_one' := Subtype.ext hone
      map_add' := fun x y => Subtype.ext (hadd x y)
      map_mul' := fun x y => Subtype.ext (hmul x y) }
  refine ⟨θ, (fun x => Subtype.ext (hstar x)), hgNorm, ?_, ?_⟩
  · exact heq (v j) (constantSeq (algebraMap ℂ A Complex.I)) (hk' .imag)
  · intro x n
    have he := heq (v x * b n) (b n * v x) (hk' (.commute x n))
    exact (show g x * quotientMap ω (b n) = quotientMap ω (b n) * g x from
      by simpa only [map_mul] using he)
end KirchbergRordam.NormUltrapower
namespace KirchbergRordam.RationalDense
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.KirchbergRordam.RationalDense.instAlgebraRat_solutions
lemma stage_countable {s : Set A} (hs : s.Countable) (n : ℕ) : (stage s n).Countable := by
  induction n with
  | zero => exact hs.union (Set.countable_range _)
  | succ n ih => exact ((ih.union ((ih.prod ih).image _)).union
      ((ih.prod ih).image _)).union (ih.image _)

lemma term_countable {s : Set A} (hs : s.Countable) : (termAlgebra s : Set A).Countable :=
  Set.countable_iUnion (stage_countable hs)
lemma subset_term (s : Set A) : s ⊆ termAlgebra s :=
  fun _ ha => mem_iUnion.mpr ⟨0,Or.inl ha⟩

theorem exists_countable_dense_star [SeparableSpace A] :
    ∃ S : StarSubalgebra ℚ A, (S : Set A).Countable ∧ Dense (S : Set A) ∧
      algebraMap ℂ A Complex.I ∈ S := by
  obtain ⟨s,hc,hd⟩ := exists_countable_dense A
  refine ⟨termAlgebra (insert (algebraMap ℂ A Complex.I) s),
    term_countable (hc.insert _), hd.mono ?_, subset_term _ (mem_insert _ _)⟩
  exact fun a ha => subset_term _ (mem_insert_of_mem _ ha)
end KirchbergRordam.RationalDense
open Topology
namespace KirchbergRordam.RationalDense
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]


attribute [local instance] OAI.KirchbergRordam.RationalDense.instAlgebraRat_solutions_1
theorem extend_complex (S : StarSubalgebra ℚ A) (hS : Dense (S : Set A))
    (f : S →+* B) (hf : UniformContinuous f)
    (hstar : ∀ x, f (star x) = star (f x))
    (hI : algebraMap ℂ A Complex.I ∈ S)
    (hfI : f ⟨algebraMap ℂ A Complex.I,hI⟩ = algebraMap ℂ B Complex.I) :
    ∃ g : A →⋆ₐ[ℂ] B, ∀ x : S, g x = f x := by
  let i : S →+* A := S.subtype.toRingHom
  have ui : IsUniformInducing i := isometry_subtype_coe.isUniformInducing
  have di : DenseRange i := hS.denseRange_val
  let g : A →+* B := IsDenseInducing.extendRingHom ui di hf
  have hg : Continuous g := (uniformContinuous_uniformly_extend ui di hf).continuous
  have he (x : S) : g x = f x :=
    IsDenseInducing.extend_eq (ui.isDenseInducing di) hf.continuous x
  have hs (x : A) : g (star x) = star (g x) := by
    refine di.induction_on x (p := fun x => g (star x) = star (g x))
      (isClosed_eq (hg.comp continuous_star) (continuous_star.comp hg)) ?_
    intro x
    change g (↑(star x) : A) = star (g (x : A))
    rw [he,he,hstar]
  have hgi : g (algebraMap ℂ A Complex.I) = algebraMap ℂ B Complex.I :=
    (he ⟨_,hI⟩).trans hfI
  have hr (r : ℝ) : g (algebraMap ℂ A (r:ℂ)) = algebraMap ℂ B (r:ℂ) := by
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r
      (p := fun r => g (algebraMap ℂ A (r:ℂ)) = algebraMap ℂ B (r:ℂ))
      (isClosed_eq (hg.comp ((continuous_algebraMap ℂ A).comp Complex.continuous_ofReal))
        ((continuous_algebraMap ℂ B).comp Complex.continuous_ofReal)) ?_
    intro q
    change g (algebraMap ℂ A ((q : ℝ) : ℂ)) = algebraMap ℂ B ((q : ℝ) : ℂ)
    rw [Complex.ofReal_ratCast]
    exact g.map_rat_algebraMap q
  have hcomplex (z : ℂ) : g (algebraMap ℂ A z) = algebraMap ℂ B z := by
    conv_lhs => rw [← Complex.re_add_im z]
    simp only [map_add,map_mul,hr,hgi]
    rw [← map_mul, ← map_add, Complex.re_add_im]
  exact ⟨{ g with map_star' := hs, commutes' := hcomplex }, he⟩
end KirchbergRordam.RationalDense

namespace KirchbergRordam.NormUltrapower
open Topology TopologicalSpace
open scoped CStarAlgebra

theorem relative_commuting_copy {A D E : Type*}
    [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E]
    [SeparableSpace A] [SeparableSpace D] [SeparableSpace E]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (φ : D →⋆ₐ[ℂ] CentralAlgebra A ω)
    (ψ : E →⋆ₐ[ℂ] CentralAlgebra A ω) :
    ∃ θ : D →⋆ₐ[ℂ] CentralAlgebra A ω,
      ∀ d e, Commute (θ d) (ψ e) := by
  classical
  let : _root_.Algebra ℚ D := Algebra.compHom D (algebraMap ℚ ℂ)
  obtain ⟨S,hcount,hden,hI⟩ := RationalDense.exists_countable_dense_star (A := D)
  let : Countable S := hcount.to_subtype
  let Φ : D →⋆ₐ[ℂ] Algebra A ω := (centralSubalgebra ω).subtype.comp φ
  let f : S →+* Algebra A ω := Φ.toRingHom.comp S.subtype.toRingHom
  have hfstar (x : S) : f (star x) = star (f x) := map_star Φ (x:D)
  have hfcent (x : S) : f x ∈ centralSubalgebra ω := (φ (x:D)).property
  have hfI : f ⟨_,hI⟩ = diagonal ω (algebraMap ℂ A Complex.I) := by
    change Φ (algebraMap ℂ D Complex.I) = _
    exact (Φ.commutes Complex.I).trans ((diagonal ω).commutes Complex.I).symm
  let e : ℕ → E := denseSeq E
  have he : DenseRange e := denseRange_denseSeq E
  have hbex (n : ℕ) : ∃ b : BoundedSeq A, quotientMap ω b = (ψ (e n) : Algebra A ω) :=
    Ideal.Quotient.mk_surjective _
  choose b hb using hbex
  obtain ⟨g,hgs,hgn,hgi,hgc⟩ := countable_reindex ω hω f hfstar hfcent ⟨_,hI⟩ hfI b
  have hbound (x : S) : ‖g x‖ ≤ ‖x‖ := by
    rw [hgn]
    exact NonUnitalStarAlgHom.norm_apply_le Φ (x:D)
  have hLip : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact hbound (x-y)
  have hgi' : g ⟨_,hI⟩ = algebraMap ℂ (CentralAlgebra A ω) Complex.I := by
    apply Subtype.ext
    exact hgi.trans ((diagonal ω).commutes Complex.I)
  obtain ⟨θ,hθ⟩ := RationalDense.extend_complex S hden g hLip.uniformContinuous hgs hI hgi'
  refine ⟨θ, fun d e' => ?_⟩
  change θ d * ψ e' = ψ e' * θ d
  have hθc : Continuous θ := map_continuous θ
  have hψc : Continuous ψ := map_continuous ψ
  refine hden.denseRange_val.induction_on d
    (p := fun d => θ d * ψ e' = ψ e' * θ d)
    (isClosed_eq (hθc.mul continuous_const) (continuous_const.mul hθc)) ?_
  intro x
  rw [hθ]
  refine he.induction_on e' (p := fun e' => g x * ψ e' = ψ e' * g x)
    (isClosed_eq (continuous_const.mul hψc) (hψc.mul continuous_const)) ?_
  intro n
  apply Subtype.ext
  change (g x : Algebra A ω) * (ψ (e n) : Algebra A ω) =
    (ψ (e n) : Algebra A ω) * (g x : Algebra A ω)
  simpa only [hb] using (hgc x n).eq
end KirchbergRordam.NormUltrapower
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SeparableReduction
attribute [-instance] _root_.OAI.KirchbergRordam.MaxTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.StarCompletion.completionNormedStarGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


namespace KirchbergRordam.GenericRW.SeparableReduction
section
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]


lemma stage_separable {s : Set A} (hs : IsSeparable s) (n : ℕ) : IsSeparable (stage s n) := by
  induction n with
  | zero => exact hs.union (isSeparable_range (continuous_algebraMap ℂ A))
  | succ n ih => exact ((ih.union ((ih.prod ih).image (continuous_fst.add continuous_snd))).union
      ((ih.prod ih).image (continuous_fst.mul continuous_snd))).union (ih.image continuous_star)
lemma adjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have ht : StarAlgebra.adjoin ℂ s ≤ termAlgebra s := StarAlgebra.adjoin_le
    (fun a ha=>mem_iUnion.mpr ⟨0,Or.inl ha⟩)
  exact (IsSeparable.iUnion (stage_separable hs)).mono ht


lemma closedAdjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set A) :=
  (adjoin_separable hs).closure
end

open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
lemma span_commutator_list {x : A} (hx : x∈DetectingSpace.commutatorIdeal (D:=A)) :
    ∃ l : List (Term A), (l.map term).sum=x := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨a,b,rfl⟩ := hx
    exact ⟨[(1,(a:A),(b:A),1)],by simp [term]⟩
  | zero => exact ⟨[],by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨l,hl⟩ := ihx
    obtain ⟨m,hm⟩ := ihy
    exact ⟨l++m,by simp [hl,hm]⟩
  | neg x hx ih =>
    obtain ⟨l,hl⟩ := ih
    refine ⟨l.map (fun t=>(-t.1,t.2)),?_⟩
    simp only [List.map_map,Function.comp_def]
    have he : (fun t : Term A=>term (-t.1,t.2))=fun t=> -(term t) := by funext t; simp [term]
    rw [he]
    have hn := congrArg (fun a : A=> -a) hl
    rw [List.sum_neg,List.map_map] at hn
    exact hn
  | left_absorb a x hx ih =>
    obtain ⟨l,hl⟩ := ih
    refine ⟨l.map (fun t=>(a*t.1,t.2)),?_⟩
    simp only [List.map_map,Function.comp_def]
    have he : (fun t : Term A=>term (a*t.1,t.2))=fun t=>a*term t := by funext t; simp [term,mul_assoc]
    rw [he,List.sum_map_mul_left,hl]
  | right_absorb b x hx ih =>
    obtain ⟨l,hl⟩ := ih
    refine ⟨l.map (fun t=>(t.1,t.2.1,t.2.2.1,t.2.2.2*b)),?_⟩
    simp only [List.map_map,Function.comp_def]
    have he : (fun t : Term A=>term (t.1,t.2.1,t.2.2.1,t.2.2.2*b))=fun t=>term t*b := by
      funext t; simp [term,mul_assoc]
    rw [he,List.sum_map_mul_right,hl]
end KirchbergRordam.GenericRW.SeparableReduction

namespace KirchbergRordam.GenericRW
open _root_.OAI.KirchbergRordam.GenericRW.SeparableReduction
open TopologicalSpace Topology


theorem separable_characterless_subalgebra (D : Type*) [CStarAlgebra D] [Nontrivial D]
    (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ S : StarSubalgebra ℂ D, IsClosed (S : Set D) ∧
      TopologicalSpace.IsSeparable (S : Set D) ∧ IsEmpty (S →⋆ₐ[ℂ] ℂ) := by
  classical
  have h1 : (1:D)∈DetectingSpace.commutatorIdeal := by
    rw [DetectingSpace.commutatorIdeal_eq_top hD]
    trivial
  obtain ⟨l,hl⟩ := span_commutator_list h1
  let entries : Term D→List D := fun t=>[t.1,t.2.1,t.2.2.1,t.2.2.2]
  let f : Finset D := (l.flatMap entries).toFinset
  let S := (StarAlgebra.adjoin ℂ (f:Set D)).topologicalClosure
  have hm (t : Term D) (ht : t∈l) {a : D} (ha : a∈entries t) : a∈S := by
    apply StarSubalgebra.le_topologicalClosure
    apply StarAlgebra.subset_adjoin
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨t,ht,ha⟩)
  let liftTerm : {t // t∈l}→Term S := fun t =>
    (⟨t.1.1,hm t.1 t.2 (by simp [entries])⟩,
     ⟨t.1.2.1,hm t.1 t.2 (by simp [entries])⟩,
     ⟨t.1.2.2.1,hm t.1 t.2 (by simp [entries])⟩,
     ⟨t.1.2.2.2,hm t.1 t.2 (by simp [entries])⟩)
  have hh : (l.attach.map (fun t=>term (liftTerm t))).sum=(1:S) := by
    apply Subtype.ext
    change S.subtype ((l.attach.map (fun t=>term (liftTerm t))).sum)=1
    rw [map_list_sum,List.map_map]
    change (l.attach.map (fun t=>term t.1)).sum=1
    rw [List.attach_map_val,hl]
  refine ⟨S,StarSubalgebra.isClosed_topologicalClosure _,
    closedAdjoin_separable f.finite_toSet.isSeparable,⟨?_⟩⟩
  intro χ
  have hk (t : Term S) : χ (term t)=0 := by
    simp only [term,map_mul,map_sub]
    rw [mul_comm (χ t.2.1) (χ t.2.2.1),sub_self,mul_zero,zero_mul]
  have hz : χ ((l.attach.map (fun t=>term (liftTerm t))).sum)=0 := by
    rw [map_list_sum,List.map_map]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    exact hk _
  rw [hh,map_one] at hz
  exact one_ne_zero hz
end KirchbergRordam.GenericRW


namespace KirchbergRordam.GenericRW.MaxTensor
open Topology TopologicalSpace
open scoped CStarAlgebra
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]


theorem separable_maxTensor [SeparableSpace A] [SeparableSpace B] :
    SeparableSpace (Algebra A B) := by
  let s : Set (Algebra A B) := Set.range (includeLeft (A := A) (B := B)) ∪
    Set.range (includeRight (A := A) (B := B))
  let T := (StarAlgebra.adjoin ℂ s).topologicalClosure
  have hsep : IsSeparable (T : Set (Algebra A B)) :=
    SeparableReduction.closedAdjoin_separable ((isSeparable_range (map_continuous includeLeft)).union
      (isSeparable_range (map_continuous includeRight)))
  have hinc : s ⊆ T := (StarAlgebra.subset_adjoin ℂ s).trans
    (StarSubalgebra.le_topologicalClosure _)
  have hall (x : Algebra A B) : x ∈ T := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact StarSubalgebra.isClosed_topologicalClosure _
    | ih x =>
      suffices ∀ tensor : A ⊗[ℂ] B, of (rawEquiv tensor) ∈ T from this x
      intro tensor
      induction tensor using OAI.tensorInductionOn with
      | tmul a b =>
        change of (a ⊗ₜ[ℂ] b) ∈ T
        rw [of_tmul]
        exact T.mul_mem (hinc (Or.inl ⟨a,rfl⟩)) (hinc (Or.inr ⟨b,rfl⟩))
      | add x y hx hy => rw [map_add, map_add]; exact T.add_mem hx hy
  exact isSeparable_univ_iff.mp (hsep.mono (fun x _ => hall x))

instance powerPack_separable (D : Type*) [CStarAlgebra D] [SeparableSpace D] (n : ℕ) :
    SeparableSpace (powerPack D n) := by
  induction n with
  | zero => exact inferInstanceAs (SeparableSpace D)
  | succ n ih =>
    let := ih
    exact separable_maxTensor (A := D) (B := powerPack D n)
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.NormUltrapower
open TopologicalSpace


theorem generic_maximal_power_to_central {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
    [SeparableSpace A] [SeparableSpace D] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (φ : D →⋆ₐ[ℂ] CentralAlgebra A ω) (n : ℕ) :
    Nonempty (GenericRW.MaxTensor.powerPack D n →⋆ₐ[ℂ] CentralAlgebra A ω) := by
  induction n with
  | zero => exact ⟨φ⟩
  | succ n ih =>
    obtain ⟨ψ⟩ := ih
    obtain ⟨θ,hθ⟩ := relative_commuting_copy ω hω φ ψ
    exact ⟨GenericRW.MaxTensor.lift θ ψ hθ⟩
end KirchbergRordam.NormUltrapower

namespace KirchbergRordam
open TopologicalSpace
omit [GenericRW.Size] [GenericRW.PauliData] in


theorem central_prime_power_drop (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    Nonempty (PrimeDimensionDrop.Algebra (2^(k+1)) (2^(k+1)+1) →⋆ₐ[ℂ]
      NormUltrapower.CentralAlgebra A ω) := by
  let : GenericRW.Size := GenericRW.powerSize k
  let : GenericRW.PauliData := GenericRW.powerPauliData k
  obtain ⟨S,hclosed,hsep,hS⟩ := GenericRW.separable_characterless_subalgebra
    (NormUltrapower.CentralAlgebra A ω) hF
  let : IsClosed (S : Set (NormUltrapower.CentralAlgebra A ω)) := hclosed
  let : CStarAlgebra S := StarSubalgebra.cstarAlgebra S
  let : SeparableSpace S := hsep.separableSpace
  obtain ⟨m,⟨φ⟩⟩ := GenericRW.finite_prime_power_drop S hS k
  obtain ⟨ψ⟩ := NormUltrapower.generic_maximal_power_to_central ω hω S.subtype m
  exact ⟨ψ.comp φ⟩
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
lemma size_two (n : ℕ) : 2≤S.size n := by
  rw [S.size_power]
  exact Nat.le_self_pow (by omega) 2
instance instNeZeroNatSize (n : ℕ) : NeZero (S.size n) := ⟨by have := S.size_two n; omega⟩
instance instNontrivialStage (n : ℕ) : Nontrivial (S.Stage n) := inferInstanceAs
  (Nontrivial (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))

instance instNontrivialObjSystem (n : ℕ) : Nontrivial (S.system.obj n) := inferInstanceAs (Nontrivial (S.Stage n))
theorem stage_to_central_oai (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [TopologicalSpace.SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) (n : ℕ) :
    Nonempty (S.Stage n →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  have aux (p : ℕ) [NeZero p] (he : p=2^(S.exponent n+1)) :
      Nonempty (PrimeDimensionDrop.Algebra p (p+1) →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
    subst p
    exact central_prime_power_drop A ω hω hF (S.exponent n)
  exact aux (S.size n) (S.size_power n)
end KirchbergRordam.PrimeDropPresentation
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KirchbergRordam.PrimeDropPresentation.stage_to_central_oai.{u_1} := @OAI.KirchbergRordam.PrimeDropPresentation.stage_to_central_oai.{u_1}
