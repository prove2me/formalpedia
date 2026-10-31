-- Prove2me | solution 1 for OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:08:34.118737+00:00
-- url     : https://prove2.me/submissions/a1c6d202-7074-4db8-85a1-629df506ee35

import Mathlib
import Definitions.Def_OAIQ019N043
import Theorems.Thm_OAI_NuclearUltrapower_VariableUltra_quotient_tensor_no_invariants

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteRepresentations
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter
noncomputable section
open scoped InnerProductSpace

namespace NuclearUltrapower

attribute [instance] FiniteUnitaryRep.normed FiniteUnitaryRep.inner
  FiniteUnitaryRep.complete FiniteUnitaryRep.finite FiniteUnitaryRep.nontrivial

variable {Γ : Type u} [Group Γ]

namespace FiniteUnitaryRep

/-- A nonzero subrepresentation of an irreducible representation is the whole. -/
theorem Embeds.equivalent_of_irreducible {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (hτ : τ.Irreducible) : π.Equivalent τ := by
  obtain ⟨T, hT⟩ := h
  have hr : ∀ g x, x ∈ T.toLinearMap.range → τ.action g x ∈ T.toLinearMap.range := by
    rintro g x ⟨y, rfl⟩
    exact ⟨π.action g y, hT g y⟩
  rcases hτ _ hr with hb | ht
  · have hz : T.toLinearMap = 0 := LinearMap.range_eq_bot.mp hb
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    have hzx : T x = 0 := congrArg (fun L : π →ₗ[ℂ] τ => L x) hz
    have := T.injective (show T x = T 0 by rw [hzx, map_zero])
    exact False.elim (hx this)
  · exact ⟨LinearIsometryEquiv.ofSurjective T (LinearMap.range_eq_top.mp ht), hT⟩

theorem restrict_embeds (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] :
    (π.restrict W hW).Embeds π :=
  ⟨W.subtypeₗᵢ, fun _ _ => rfl⟩

/-- Every nonzero finite-dimensional unitary representation has an irreducible
subrepresentation. This uses minimal dimension, not a semisimplicity assumption. -/
theorem exists_irreducible (π : FiniteUnitaryRep.{u,v} Γ) :
    ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ τ.Embeds π := by
  let P (n : ℕ) := ∃ W : Submodule ℂ π, W ≠ ⊥ ∧
    (∀ g x, x ∈ W → π.action g x ∈ W) ∧ Module.finrank ℂ W = n
  have hP : ∃ n, P n := ⟨Module.finrank ℂ (⊤ : Submodule ℂ π),
    ⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top, rfl⟩
  classical
  obtain ⟨W, hW0, hW, hdim⟩ := Nat.find_spec hP
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  refine ⟨π.restrict W hW, ?_, π.restrict_embeds W hW⟩
  intro V hV
  change Submodule ℂ W at V
  by_cases hV0 : V = ⊥
  · exact Or.inl hV0
  right
  let U : Submodule ℂ π := V.map W.subtype
  have hU0 : U ≠ ⊥ := by
    intro hU
    apply hV0
    apply le_antisymm ?_ bot_le
    intro x hx
    have hmem : (x : π) ∈ U := ⟨x, hx, rfl⟩
    rw [hU] at hmem
    exact W.subtype_injective hmem
  have hU (g : Γ) (x : π) (hx : x ∈ U) : π.action g x ∈ U := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(π.restrict W hW).action g y, hV g y hy, rfl⟩
  have heq : Module.finrank ℂ U = Module.finrank ℂ V :=
    LinearEquiv.finrank_eq (V.equivMapOfInjective W.subtype W.subtype_injective).symm
  have hmin : Nat.find hP ≤ Module.finrank ℂ V := by
    rw [← heq]
    exact Nat.find_min' hP ⟨U, hU0, hU, rfl⟩
  have he : Module.finrank ℂ V = Module.finrank ℂ (π.restrict W hW) := by
    apply le_antisymm (Submodule.finrank_le V)
    exact hdim ▸ hmin
  exact Submodule.eq_top_of_finrank_eq he

end FiniteUnitaryRep
end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Schur
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
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
namespace NuclearUltrapower
namespace FiniteUnitaryRep
open Module.End
variable {Γ : Type u} [Group Γ]

/-- Schur's scalar lemma, proved from an actual eigenvalue over C. -/
theorem scalar_of_commuting {π : FiniteUnitaryRep.{u,v} Γ} (hπ : π.Irreducible)
    (T : π →ₗ[ℂ] π) (hT : ∀ g x, T (π.action g x) = π.action g (T x)) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  have hi : ∀ g x, x ∈ eigenspace T c → π.action g x ∈ eigenspace T c := by
    intro g x hx
    rw [mem_eigenspace_iff] at hx ⊢
    rw [hT, hx, map_smul]
  rcases hπ _ hi with hz | ht
  · exact False.elim ((Module.End.hasEigenvalue_iff.mp hc) hz)
  · refine ⟨c, ?_⟩
    ext x
    exact (mem_eigenspace_iff.mp (show x ∈ eigenspace T c by rw [ht]; trivial))

/-- Every nonzero intertwiner out of an irreducible finite-dimensional unitary
representation is a positive scalar multiple of an isometry. The target can
be any Hilbert space, not necessarily separable or finite-dimensional. -/
theorem isometry_of_intertwiner {π : FiniteUnitaryRep.{u,v} Γ} (hπ : π.Irreducible)
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (T : π →L[ℂ] K) (hT0 : T ≠ 0)
    (hT : ∀ g x, T (π.action g x) = σ g (T x)) :
    ∃ U : π →ₗᵢ[ℂ] K, ∀ g x, U (π.action g x) = σ g (U x) := by
  have hcomm (g : Γ) (y : π) :
      T.adjoint (T (π.action g y)) = π.action g (T.adjoint (T y)) := by
    apply ext_inner_left ℂ
    intro z
    obtain ⟨x, rfl⟩ := (π.action g).surjective z
    rw [ContinuousLinearMap.adjoint_inner_right, hT, hT,
      (σ g).inner_map_map, (π.action g).inner_map_map,
      ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨c, hc⟩ := scalar_of_commuting hπ (T.adjoint.comp T).toLinearMap hcomm
  have hn (x : π) : ‖T x‖ ^ 2 = RCLike.re c * ‖x‖ ^ 2 := by
    have he := congrArg (fun L : π →ₗ[ℂ] π => RCLike.re (Inner.inner ℂ x (L x))) hc
    change RCLike.re (Inner.inner ℂ x (T.adjoint (T x))) =
      RCLike.re (Inner.inner ℂ x (c • x)) at he
    simpa only [ContinuousLinearMap.adjoint_inner_right, inner_smul_right,
      RCLike.mul_re, inner_self_eq_norm_sq, inner_self_im, mul_zero, sub_zero] using he
  have hex : ∃ x : π, T x ≠ 0 := by
    by_contra! h
    exact hT0 (ContinuousLinearMap.ext fun x => h x)
  obtain ⟨x, hx⟩ := hex
  have hcpos : 0 < RCLike.re c := by
    have hh := hn x
    have hhpos : 0 < ‖T x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    nlinarith [sq_nonneg ‖x‖]
  let r : ℝ := Real.sqrt (RCLike.re c)
  have hr : 0 < r := Real.sqrt_pos.mpr hcpos
  have hnorm (x : π) : ‖T x‖ = r * ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hr.le (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hcpos.le]
    exact hn x
  let U : π →ₗᵢ[ℂ] K := {
    toLinearMap := (↑r⁻¹ : ℂ) • T.toLinearMap
    norm_map' x := by
      change ‖(↑r⁻¹ : ℂ) • T x‖ = ‖x‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hnorm]
      rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] }
  refine ⟨U, fun g x => ?_⟩
  change (↑r⁻¹ : ℂ) • T (π.action g x) = σ g ((↑r⁻¹ : ℂ) • T x)
  rw [hT, map_smul]

/-- The unitary form of Schur's lemma used by the coordinate-quotient argument. -/
theorem equivalent_of_nonzero_intertwiner {π τ : FiniteUnitaryRep.{u,v} Γ}
    (hπ : π.Irreducible) (hτ : τ.Irreducible) (T : π →L[ℂ] τ) (hT0 : T ≠ 0)
    (hT : ∀ g x, T (π.action g x) = τ.action g (T x)) : π.Equivalent τ :=
  Embeds.equivalent_of_irreducible (isometry_of_intertwiner hπ τ.action T hT0 hT) hτ

end FiniteUnitaryRep

open scoped TensorProduct
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {Γ : Type u} [Group Γ]

section MixedTensor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Tensor invariance is the genuine intertwining equation. -/
theorem mixedTensorOperator_action (u : E ≃ₗᵢ[ℂ] E) (v : F ≃ₗᵢ[ℂ] F)
    (z : E ⊗[ℂ] StrongDual ℂ F) :
    mixedTensorOperator (TensorProduct.congrIsometry u (dualUnitary v) z) =
      (u : E →L[ℂ] E).comp ((mixedTensorOperator z).comp (v.symm : F →L[ℂ] F)) := by
  induction z using OAI.tensorInductionOn with
  | tmul x f => ext y; simp
  | add x y hx hy => simp only [map_add, hx, hy, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

/-- The invariant tensor defines an actual bounded intertwiner. -/
theorem invariant_tensor_intertwines
    (ρ : Γ →* (E ≃ₗᵢ[ℂ] E)) (π : Γ →* (F ≃ₗᵢ[ℂ] F))
    (z : E ⊗[ℂ] StrongDual ℂ F)
    (hz : ∀ g, tensorContragredientRep ρ π g z = z) (g : Γ) (x : F) :
    mixedTensorOperator z (π g x) = ρ g (mixedTensorOperator z x) := by
  have he := congrArg (fun w => mixedTensorOperator w (π g x)) (hz g)
  change mixedTensorOperator (TensorProduct.congrIsometry (ρ g) (dualUnitary (π g)) z) (π g x) = _ at he
  rw [mixedTensorOperator_action] at he
  simpa using he.symm

end MixedTensor

/-- Schur exclusion at each nonexceptional coordinate. -/
theorem tensor_no_invariants_of_inequivalent
    {π τ : FiniteUnitaryRep.{u,v} Γ} (hπ : π.Irreducible) (hτ : τ.Irreducible)
    (hne : ¬ τ.Equivalent π) (z : π ⊗[ℂ] StrongDual ℂ τ)
    (hz : ∀ g, tensorContragredientRep π.action τ.action g z = z) : z = 0 := by
  by_contra h0
  have hT : mixedTensorOperator z ≠ 0 := by
    intro h
    apply h0
    exact mixedTensorOperator_injective (by simpa using h)
  exact hne (FiniteUnitaryRep.equivalent_of_nonzero_intertwiner hτ hπ
    (mixedTensorOperator z) hT (invariant_tensor_intertwines π.action τ.action z hz))

end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section TensorSurjective
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- Every operator with finite-dimensional domain is represented by an actual
algebraic tensor; no completed-tensor compactness argument is hidden here. -/
theorem mixedTensorOperator_surjective :
    Function.Surjective (mixedTensorOperator (E := E) (F := F)) := by
  intro T
  let b := stdOrthonormalBasis ℂ F
  refine ⟨∑ i, T (b i) ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ F (b i), ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp only [map_sum, sum_apply, mixedTensorOperator_tmul]
  change (∑ i, inner ℂ (b i) x • T (b i)) = T x
  calc
    _ = T (∑ i, inner ℂ (b i) x • b i) := by simp only [map_sum, map_smul]
    _ = T x := congrArg T (b.sum_repr' x)

/-- A nonzero finite-dimensional intertwiner gives a nonzero invariant tensor. -/
theorem exists_invariant_tensor_of_intertwiner {Γ : Type*} [Group Γ]
    (ρ : Γ →* (E ≃ₗᵢ[ℂ] E)) (π : Γ →* (F ≃ₗᵢ[ℂ] F))
    (T : F →L[ℂ] E) (hT : T ≠ 0)
    (hcomm : ∀ g x, T (π g x) = ρ g (T x)) :
    ∃ z : E ⊗[ℂ] StrongDual ℂ F, z ≠ 0 ∧
      ∀ g, tensorContragredientRep ρ π g z = z := by
  obtain ⟨z, hz⟩ := mixedTensorOperator_surjective (E := E) T
  refine ⟨z, ?_, ?_⟩
  · intro h0
    apply hT
    simpa only [h0, map_zero] using hz.symm
  · intro g
    apply mixedTensorOperator_injective
    change mixedTensorOperator (TensorProduct.congrIsometry (ρ g) (dualUnitary (π g)) z) = _
    rw [mixedTensorOperator_action, hz]
    apply ContinuousLinearMap.ext
    intro x
    change ρ g (T ((π g).symm x)) = T x
    rw [← hcomm, (π g).apply_symm_apply]
end TensorSurjective

section FiniteSubspace
variable {Γ : Type u} [Group Γ]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (σ : Γ →* (K ≃ₗᵢ[ℂ] K))
  (W : Submodule ℂ K) [Nontrivial W] [FiniteDimensional ℂ W]
  (hW : ∀ g x, x ∈ W → σ g x ∈ W)

include W hW in
/-- Every nonzero finite subrepresentation contains an irreducible one, with
an explicit isometric intertwiner into the original ambient Hilbert space. -/
theorem finiteSubspace_exists_irreducible :
    ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧
      ∃ T : τ →ₗᵢ[ℂ] K, ∀ g x, T (τ.action g x) = σ g (T x) := by
  obtain ⟨τ, hτ, T, hT⟩ := (finiteSubspaceRep σ W hW).exists_irreducible
  refine ⟨τ, hτ, W.subtypeₗᵢ.comp T, ?_⟩
  intro g x
  exact congrArg (fun y : W => (y : K)) (hT g x)
end FiniteSubspace
end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_RepresentationUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
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
namespace NuclearUltrapower
open scoped TensorProduct

namespace VariableUltra
variable {ι : Type*} {Γ : Type u} [Group Γ]
variable (π : ι → FiniteUnitaryRep.{u,v} Γ)

variable (ω : Ultrafilter ι) {K : Type v}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An inequivalent sequence has at most one coordinate of any fixed type. -/
theorem eventually_inequivalent
    (hω : ∀ i : ι, ({i} : Set ι) ∉ (ω : Filter ι))
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (τ : FiniteUnitaryRep.{u,v} Γ) :
    ∀ᶠ i in (ω : Filter ι), ¬ τ.Equivalent (π i) := by
  classical
  by_cases he : ∃ i, τ.Equivalent (π i)
  · obtain ⟨i, hi⟩ := he
    have hiω : ∀ᶠ j in (ω : Filter ι), j ≠ i :=
      show {j | j ≠ i} ∈ (ω : Filter ι) from
        (ω.compl_mem_iff_notMem.mpr (hω i))
    filter_upwards [hiω] with j hj
    intro hjτ
    exact hne hj (hjτ.symm.trans hi)
  · exact Filter.Eventually.of_forall (fun i h => he ⟨i, h⟩)

/-- The ordinary finite-dimensional tensor gap at a nonexceptional coordinate. -/
theorem inequivalent_tensor_gap (P T : FiniteUnitaryRep.{u,v} Γ)
    (hP : P.Irreducible) (hT : T.Irreducible) (hne : ¬ T.Equivalent P)
    (S : Finset Γ) (κ : ℝ) (hgap : HasKazhdanGap.{u,v} S κ) :
    ∀ w : P ⊗[ℂ] StrongDual ℂ T, κ * ‖w‖ ^ 2 ≤ ∑ s ∈ S,
      ‖TensorProduct.congrIsometry (P.action s) (dualUnitary (T.action s)) w - w‖ ^ 2 := by
  let ρ := tensorContragredientRep P.action T.action
  have hρ : ∀ w : P ⊗[ℂ] StrongDual ℂ T, (∀ g : Γ, ρ g w = w) → w = 0 :=
    tensor_no_invariants_of_inequivalent hP hT hne
  have he := hgap (P ⊗[ℂ] StrongDual ℂ T) ρ hρ
  exact he

/-- The varying matrix quotient has no finite-dimensional parts in any
unital representation. This is the hard quotient step of nuclear-finiteness. -/
theorem quotientRepresentation_weakly_mixing_oai
    (hω : ∀ i : ι, ({i} : Set ι) ∉ (ω : Filter ι))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (S : Finset Γ) (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    HasNoFiniteDimensionalSubrep (quotientRepresentation π ω φ) := by
  classical
  intro W hW0 hW hfd
  let : FiniteDimensional ℂ W := hfd
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨τ, hτ, T, hT⟩ := finiteSubspace_exists_irreducible
    (quotientRepresentation π ω φ) W hW
  have hT0 : T.toContinuousLinearMap ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : τ)
    apply hx
    apply T.injective
    change T.toContinuousLinearMap x = T.toContinuousLinearMap 0
    rw [he]
    rfl
  obtain ⟨z, hz0, hz⟩ := exists_invariant_tensor_of_intertwiner
    (quotientRepresentation π ω φ) τ.action T.toContinuousLinearMap hT0 hT
  have hcoord : ∀ᶠ i in (ω : Filter ι), ∀ w : π i ⊗[ℂ] StrongDual ℂ τ,
      κ * ‖w‖ ^ 2 ≤ ∑ s ∈ S,
        ‖TensorProduct.congrIsometry ((π i).action s) (dualUnitary (τ.action s)) w - w‖ ^ 2 := by
    filter_upwards [eventually_inequivalent π ω hω hne τ] with i hi
    exact inequivalent_tensor_gap (π i) τ (hirr i) hτ hi S κ hgap
  have hn : Nonempty (Fin (Module.finrank ℂ (StrongDual ℂ τ))) :=
    Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := ℂ) (M := StrongDual ℂ τ))
  let := hn
  exact hz0 (quotient_tensor_no_invariants (fun i => π i) ω S
    (stdOrthonormalBasis ℂ (StrongDual ℂ τ)) (fun i => (π i).action)
    (fun s => dualUnitary (τ.action s)) hκ0 hκ hcoord φ z (fun s _ => hz s))
end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing_oai.{u, v, u_1} := @OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing_oai.{u, v, u_1}
