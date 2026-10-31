-- Prove2me | solution 1 for OAI.NuclearUltrapower.matchClasses_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:34:45.40338+00:00
-- url     : https://prove2.me/submissions/475067ae-ff8e-4c5c-a666-ffc915ea5503

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N043
import Theorems.Thm_OAI_NuclearUltrapower_nuclear_coordinate_bound

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertTensor
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower

section TensorOperators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable [CompleteSpace E] [CompleteSpace F]

theorem tensorLeftRight_mul (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    tensorLeftHom U * tensorRightHom V = completedTensorMap U V := by
  change completedTensorMap U 1 * completedTensorMap 1 V = _
  rw [← completedTensorMap_mul, mul_one, one_mul]

end TensorOperators
end NuclearUltrapower

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Laplacian
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace NuclearUltrapower

section Operator
variable {Γ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The quadratic form is exactly the energy, with no representation relations. -/
theorem laplacian_inner (S : Finset Γ) (u : Γ → (H →L[ℂ] H)) (x : H) :
    inner ℂ x (laplacian S u x) = (∑ s ∈ S, ‖u s x - x‖ ^ 2 : ℝ) := by
  simp only [laplacian, sum_apply, inner_sum, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp [inner_self_eq_norm_sq_to_K]

end Operator
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SpatialGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder

section ComplementPolynomial
variable {Γ A : Type*} [CStarAlgebra A]

/-- Polynomial form of the complemented Laplacian, retaining arbitrary unitary tuples. -/
theorem laplacian_complement_expand (S : Finset Γ) (u : Γ → unitary A) :
    (4 * (S.card : ℝ)) • (1 : A) - laplacian S (fun s => (u s : A)) =
      (2 * (S.card : ℝ)) • (1 : A) + ∑ s ∈ S, ((u s : A) + star (u s : A)) := by
  have hs (s : Γ) : star ((u s : A) - 1) * ((u s : A) - 1) =
      (2 : ℝ) • (1 : A) - ((u s : A) + star (u s : A)) := by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one,
      Unitary.coe_star_mul_self]
    module
  simp only [laplacian, hs, Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  module
end ComplementPolynomial

end NuclearUltrapower

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v
open Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder
namespace NuclearUltrapower
section NuclearFiniteness
variable {Γ : Type u} [Group Γ] {B : Type v} [CStarAlgebra B]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

/-- Quantitative finiteness obstruction: an inequivalent irreducible sequence
cannot have a uniformly small spectral minimum for a fixed nuclear tuple. -/
theorem nuclear_no_inequivalent_matches
    (hB : IsNuclear.{v,v} B) (S : Finset Γ) (κ a : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ ^ 2 / (4 * (S.card : ℝ)))
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (u : Γ → unitary B)
    (hsmall : ∀ i, 4 * (S.card : ℝ) - a < ‖coordinateComplement ρ π S u i‖) : False := by
  have hb := nuclear_coordinate_bound ρ π ω hB S κ hS hκ0 hκ hgap hω hirr hne u
  have hl := HilbertUltraproduct.map_norm_tendsto ω (coordinateComplement ρ π S u)
  have he : 4 * (S.card : ℝ) - a ≤
      ‖finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u)‖ :=
    ge_of_tendsto hl (Filter.Eventually.of_forall fun i => (hsmall i).le)
  linarith
end NuclearFiniteness
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v
open scoped InnerProductSpace ComplexOrder TensorProduct
namespace NuclearUltrapower
section EnergyNorm
theorem complex_real_card_smul {A : Type*} [CStarAlgebra A] (n : ℕ) :
    (2 * (n : ℂ)) • (1 : A) = (2 * (n : ℝ)) • (1 : A) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp

variable {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_complement_gt_of_energy_lt (S : Finset J) (U : J → unitary (H →L[ℂ] H))
    (a : ℝ) (x : H) (hx : ‖x‖ = 1)
    (he : (∑ s ∈ S, ‖(U s : H →L[ℂ] H) x - x‖ ^ 2) < a) :
    4 * (S.card : ℝ) - a < ‖(4 * (S.card : ℝ)) • (1 : H →L[ℂ] H) -
      laplacian S (fun s => (U s : H →L[ℂ] H))‖ := by
  let C : H →L[ℂ] H := (4 * (S.card : ℝ)) • 1 - laplacian S (fun s => (U s : H →L[ℂ] H))
  have hinner : (inner ℂ x (C x)).re = 4 * (S.card : ℝ) -
      ∑ s ∈ S, ‖(U s : H →L[ℂ] H) x-x‖^2 := by
    dsimp only [C]
    rw [sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, Complex.sub_re, inner_smul_right_eq_smul]
    rw [laplacian_inner]
    simp [inner_self_eq_norm_sq_to_K, hx]
    norm_cast
  have hle : (inner ℂ x (C x)).re ≤ ‖C‖ := by
    have hi := (Complex.re_le_norm (inner ℂ x (C x))).trans (norm_inner_le_norm x (C x))
    have ho := C.le_opNorm x
    rw [hx,one_mul] at hi
    rw [hx,mul_one] at ho
    exact hi.trans ho
  rw [hinner] at hle
  exact (sub_lt_sub_left he _).trans_le hle

end EnergyNorm
section Matching
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
theorem Matches.norm_complement {a : ℝ} {π : FiniteUnitaryRep.{u,v} Γ}
    (h : Matches ρ S u a π) :
    4 * (S.card : ℝ) - a < ‖(4 * (S.card : ℝ)) • (1 : TensorHilbert E π →L[ℂ] TensorHilbert E π) -
      laplacian S (fun s => completedTensorMap (ρ (u s)) (π.action s : π →L[ℂ] π))‖ := by
  obtain ⟨x,hx,he⟩ := h
  exact norm_complement_gt_of_energy_lt S (matchingUnitary ρ u π) a x hx he

private theorem coordinateComplement_poly (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (i : ℕ) :
    coordinateComplement ρ π S u i =
      complementPoly S (fun groupElement => tensorLeftHom (F := π i) (ρ (u groupElement)))
        (fun groupElement => tensorRightHom (E := E)
          ((π i).action groupElement : π i →L[ℂ] π i)) := by
  change (VariableUltra.eval (fun j => TensorHilbert E (π j) →L[ℂ] TensorHilbert E (π j)) i) (complementPoly S
    (fun g => tensorLeftSequence (F := fun i => π i) ρ (u g))
    (rightRepSequence (E := E) π)) = _
  rw [map_complementPoly]
  rfl

theorem coordinateComplement_apply (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (i : ℕ) :
    coordinateComplement ρ π S u i =
      (4 * (S.card : ℝ)) • (1 : TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) -
        laplacian S (fun s => completedTensorMap (ρ (u s)) ((π i).action s : π i →L[ℂ] π i)) := by
  have he := laplacian_complement_expand (A := TensorHilbert E (π i) →L[ℂ] TensorHilbert E (π i)) S (matchingUnitary ρ u (π i))
  simp only [matchingUnitary_val] at he
  rw [he, coordinateComplement_poly]
  simp only [complementPoly, ← map_star, tensorLeftRight_mul,
    ← completedTensorMap_star]
  congr 1
  exact complex_real_card_smul S.card

/-- The full class-valued finiteness conclusion for an arbitrary nuclear tuple.
This does not assert any group relation for the tuple. -/
theorem matchClasses_finite_oai (ω : Ultrafilter ℕ)
    (hB : IsNuclear.{v,v} B) (κ a : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ ^ 2 / (4 * (S.card : ℝ)))
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ)) :
    (matchClasses ρ S u a).Finite := by
  classical
  by_contra hinf
  let f := Set.Infinite.natEmbedding (matchClasses ρ S u a) hinf
  have hex (i : ℕ) : ∃ π : FiniteUnitaryRep.{u,v} Γ,
      π.Irreducible ∧ Matches ρ S u a π ∧
      Quotient.mk (FiniteUnitaryRep.classSetoid Γ) π = (f i).1 := (f i).2
  choose π hirr hm he using hex
  have hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)) := by
    intro i j hij heq
    have hq := Quotient.sound (s := FiniteUnitaryRep.classSetoid Γ) heq
    rw [he i,he j] at hq
    exact hij (f.injective (Subtype.ext hq))
  apply nuclear_no_inequivalent_matches ρ π ω hB S κ a hS hκ0 hκ hgap ha hω hirr hne u
  intro i
  rw [coordinateComplement_apply]
  exact Matches.norm_complement ρ S u (hm i)

end Matching
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.NuclearUltrapower.matchClasses_finite_oai.{u, v} := @OAI.NuclearUltrapower.matchClasses_finite_oai.{u, v}
