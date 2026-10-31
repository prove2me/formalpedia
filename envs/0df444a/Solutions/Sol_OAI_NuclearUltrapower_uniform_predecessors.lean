-- Prove2me | solution 1 for OAI.NuclearUltrapower.uniform_predecessors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:38:04.149985+00:00
-- url     : https://prove2.me/submissions/9521ed63-d271-49c6-be4d-15d4ff26bc40

import Mathlib
import Definitions.Def_OAIQ019N043
import Theorems.Thm_OAI_NuclearUltrapower_matched_vectors

section
-- module Solutions.OAIQ019_Nuc.Compat
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v

section Induction
variable {G : Type u} [Group G] (H : Subgroup G)

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

/-- Translation of a coordinate to the identity has cocycle one. -/
theorem induced_translate_coordinate (i : G ⧸ H)
    (x : lp (fun _ : G ⧸ H => V) 2) :
    inducedUnitary H α (cosetRep H i)⁻¹ x (QuotientGroup.mk 1) = x i := by
  rw [inducedUnitary_apply, inv_inv, cosetRep_smul_identity]
  have hc : cosetCocycle H (cosetRep H i)⁻¹ i = 1 := by
    apply Subtype.ext
    have hi : (cosetRep H i)⁻¹ • i = (QuotientGroup.mk 1 : G ⧸ H) := by
      calc
        _ = (cosetRep H i)⁻¹ • (cosetRep H i • (QuotientGroup.mk 1 : G ⧸ H)) :=
          congrArg (fun j : G ⧸ H => (cosetRep H i)⁻¹ • j) (cosetRep_smul_identity H i).symm
        _ = _ := inv_smul_smul _ _
    simp [cosetCocycle, hi]
  rw [hc, map_one]
  rfl

end Induction
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteRepresentations
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem restrict_embeds (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] :
    (π.restrict W hW).Embeds π :=
  ⟨W.subtypeₗᵢ, fun _ _ => rfl⟩

end FiniteUnitaryRep
end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Schur
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
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

end FiniteUnitaryRep

open scoped TensorProduct

end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.supportComplete _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ENNReal
namespace NuclearUltrapower
universe u

section FiniteInduction
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Finite (Γ ⧸ H)]
    (α : FiniteUnitaryRep.{u,u} H)

theorem identityCoordinate_intertwines (h : H) (x : finiteInduced H α) :
    identityCoordinate H α ((finiteInduced H α).action h x) =
      α.action h (identityCoordinate H α x) :=
  induced_identity_coordinate H α.action h x

/-- Every nonzero subrepresentation of a finite induction has a nonzero
identity-coordinate map. This is the all-constituent point in Frobenius reciprocity. -/
theorem identityCoordinate_nonzero {σ : FiniteUnitaryRep.{u,u} Γ}
    (U : σ →ₗᵢ[ℂ] finiteInduced H α)
    (hU : ∀ g x, U (σ.action g x) = (finiteInduced H α).action g (U x)) :
    (identityCoordinate H α).comp U.toContinuousLinearMap ≠ 0 := by
  intro hz
  obtain ⟨w,hw⟩ := exists_ne (0 : σ)
  have hUw : U w ≠ 0 := by simpa only [← map_zero U] using U.injective.ne hw
  have hex : ∃ i : Γ ⧸ H, Subtype.val (U w) i ≠ 0 := by
    by_contra! hn
    exact hUw (lp.ext (funext hn))
  obtain ⟨i,hi⟩ := hex
  have h := congrArg (fun T : σ →L[ℂ] α => T (σ.action (cosetRep H i)⁻¹ w)) hz
  change identityCoordinate H α (U (σ.action (cosetRep H i)⁻¹ w)) = 0 at h
  rw [hU] at h
  exact hi ((induced_translate_coordinate H α.action i (U w)).symm.trans h)

theorem frobenius_all_constituents (hα : α.Irreducible)
    {σ : FiniteUnitaryRep.{u,u} Γ} (hσ : σ.Embeds (finiteInduced H α)) :
    α.Embeds (restrictSubgroup H σ) := by
  obtain ⟨U,hU⟩ := hσ
  let F : σ →L[ℂ] α := (identityCoordinate H α).comp U.toContinuousLinearMap
  have hF0 : F ≠ 0 := identityCoordinate_nonzero H α U hU
  have hF (g : H) (x : σ) : F (σ.action g x) = α.action g (F x) := by
    dsimp only [F, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [hU, identityCoordinate_intertwines]
  have hstar : F.adjoint ≠ 0 := by
    intro h
    apply hF0
    have hh := congrArg ContinuousLinearMap.adjoint h
    simpa only [ContinuousLinearMap.adjoint_adjoint, map_zero] using hh
  apply FiniteUnitaryRep.isometry_of_intertwiner hα (restrictSubgroup H σ).action F.adjoint hstar
  intro g x
  change F.adjoint (α.action g x) = σ.action g (F.adjoint x)
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨z,rfl⟩ := (σ.action g).surjective y
  rw [hF, (α.action g).inner_map_map, (σ.action g).inner_map_map,
    ContinuousLinearMap.adjoint_inner_right]

end FiniteInduction
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
section Projection
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (W : Submodule ℂ F) [CompleteSpace W]

theorem tensorProjection_norm_sq (x : TensorHilbert E F) :
    ‖x‖^2 = ‖tensorProjection (E := E) W x‖^2 +
      ‖tensorProjection (E := E) Wᗮ x‖^2 := by
  let P := completedTensorMap (1 : E →L[ℂ] E) W.starProjection
  let Q := completedTensorMap (1 : E →L[ℂ] E) Wᗮ.starProjection
  have hsum : P + Q = 1 := by
    rw [← completedTensorMap_add_right]
    have h : W.starProjection + Wᗮ.starProjection = 1 := by
      ext x
      exact Submodule.starProjection_add_starProjection_orthogonal x
    rw [h,completedTensorMap_one]
  have hPQ : P*Q = 0 := by
    dsimp only [P,Q]
    rw [← completedTensorMap_mul, one_mul]
    have h : W.starProjection * Wᗮ.starProjection = 0 := by
      rw [Submodule.starProjection_orthogonal', mul_sub, mul_one]
      rw [W.isIdempotentElem_starProjection.eq]
      exact sub_self _
    rw [h]
    simp [completedTensorMap]
  have hPstar : star P = P := by
    dsimp only [P]
    rw [← completedTensorMap_star, star_one]
    congr 1
    exact isSelfAdjoint_starProjection W
  have hi : inner ℂ (P x) (Q x) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x ((star P * Q) x) = 0
    rw [hPstar,hPQ]
    simp
  have hp : ‖P x‖ = ‖tensorProjection (E := E) W x‖ := by
    dsimp only [P]
    rw [← tensorInclusion_projection]
    exact (tensorInclusion (E := E) W).norm_map _
  have hq : ‖Q x‖ = ‖tensorProjection (E := E) Wᗮ x‖ := by
    dsimp only [Q]
    rw [← tensorInclusion_projection]
    exact (tensorInclusion (E := E) Wᗮ).norm_map _
  have hs : P x + Q x = x := by
    change (P+Q) x = x
    rw [hsum]
    rfl
  rw [← hp,← hq, sq, sq, sq, ← norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (Q x) hi, hs]

end Projection
end NuclearUltrapower
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped InnerProductSpace ENNReal
namespace NuclearUltrapower
universe u v
section Coordinates
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ)
  {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

theorem coordinateInclusion_action (g : Γ) (i : Γ ⧸ H) (v : V) :
    inducedUnitary H α g (coordinateInclusion H i v) =
      coordinateInclusion H (g • i) (α (cosetCocycle H g i) v) := by
  classical
  ext j
  rw [inducedUnitary_apply, coordinateInclusion_apply, coordinateInclusion_apply]
  by_cases hj : j = g • i
  · subst j
    simp
  · have hh : g⁻¹ • j ≠ i := by
      intro he
      exact hj (by simpa only [smul_inv_smul] using congrArg (fun k : Γ ⧸ H => g • k) he)
    simp only [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hh, map_zero]

theorem cosetCocycle_factor (g : Γ) (i : Γ ⧸ H) :
    g * cosetRep H i = cosetRep H (g • i) * (cosetCocycle H g i : Γ) := by
  simp only [cosetCocycle]
  group

end Coordinates
section FiniteCoordinates
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Finite (Γ ⧸ H)]
  (α : FiniteUnitaryRep.{u,u} H)

theorem identityCoordinate_norm_le : ‖identityCoordinate H α‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖Subtype.val (x : lp (fun _ : Γ ⧸ H => α) 2) (QuotientGroup.mk 1)‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x (QuotientGroup.mk 1)

end FiniteCoordinates
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace NuclearUltrapower
variable {Γ : Type u} {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tupleEnergy_smul (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (c : ℂ) (x : E) :
    tupleEnergy S U (c • x) = ‖c‖ ^ 2 * tupleEnergy S U x := by
  simp only [tupleEnergy, map_smul, ← smul_sub, norm_smul, mul_pow, Finset.mul_sum]

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
theorem subspace_projection_intertwines {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (U : H ≃ₗᵢ[ℂ] H) (V : W ≃ₗᵢ[ℂ] W) (h : ∀ z : W, (V z : H) = U z) :
    W.orthogonalProjectionOnto.comp (U : H →L[ℂ] H) =
      (V : W →L[ℂ] W).comp W.orthogonalProjectionOnto := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  obtain ⟨z,rfl⟩ := V.surjective y
  change Inner.inner ℂ (V z) (W.orthogonalProjectionOnto (U x)) =
    Inner.inner ℂ (V z) (V (W.orthogonalProjectionOnto x))
  rw [W.inner_orthogonalProjectionOnto_eq_of_mem_left, h, U.inner_map_map,
    V.inner_map_map, W.inner_orthogonalProjectionOnto_eq_of_mem_left]

namespace FiniteUnitaryRep
variable {Γ : Type u} [Group Γ] (π : FiniteUnitaryRep.{u,v} Γ)
    (W : Submodule ℂ π) (hW : ∀ g x, x ∈ W → π.action g x ∈ W)

include hW

theorem projection_action [Nontrivial W] (g : Γ) :
    W.orthogonalProjectionOnto.comp (π.action g : π →L[ℂ] π) =
      ((π.restrict W hW).action g : π.restrict W hW →L[ℂ] π.restrict W hW).comp W.orthogonalProjectionOnto := by
  exact subspace_projection_intertwines W (π.action g) ((π.restrict W hW).action g)
    (fun _ => rfl)

end FiniteUnitaryRep
section MatchSubrep
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
/-- Normalized and homogeneous strict Rayleigh inequalities agree. -/
theorem matches_iff_homogeneous (a : ℝ) (π : FiniteUnitaryRep.{u,v} Γ) :
    Matches ρ S u a π ↔ ∃ x : TensorHilbert E π,
      tupleEnergy S (matchingTuple ρ u π) x < a * ‖x‖^2 := by
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨x, by simpa only [hx,one_pow,mul_one] using he⟩
  rintro ⟨x,hx⟩
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp [tupleEnergy] at hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨(‖x‖⁻¹ : ℂ) • x, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  rw [tupleEnergy_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have h := mul_lt_mul_of_pos_left hx (sq_pos_of_pos (inv_pos.mpr hn))
  calc
    _ < ‖x‖⁻¹^2 * (a * ‖x‖^2) := h
    _ = a := by field_simp

end MatchSubrep
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section Intertwine
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
theorem tensor_intertwining {π τ : FiniteUnitaryRep.{u,v} Γ} (T : π →L[ℂ] τ)
    (hT : ∀ g x, T (π.action g x) = τ.action g (T x)) (g : Γ)
    (x : TensorHilbert E π) :
    tensorMapBetween (1 : E →L[ℂ] E) T (matchingTuple ρ u π g x) =
      matchingTuple ρ u τ g (tensorMapBetween (1 : E →L[ℂ] E) T x) := by
  have ht : T.comp (π.action g : π →L[ℂ] π) =
      (τ.action g : τ →L[ℂ] τ).comp T := ContinuousLinearMap.ext (hT g)
  have he : (tensorMapBetween (1 : E →L[ℂ] E) T).comp
      (matchingTuple ρ u π g : TensorHilbert E π →L[ℂ] TensorHilbert E π) =
      (matchingTuple ρ u τ g : TensorHilbert E τ →L[ℂ] TensorHilbert E τ).comp
      (tensorMapBetween (1 : E →L[ℂ] E) T) := by
    rw [matchingTuple_toCLM, matchingTuple_toCLM]
    change (tensorMapBetween (1 : E →L[ℂ] E) T).comp
      (tensorMapBetween (ρ (u g)) (π.action g : π →L[ℂ] π)) =
        (tensorMapBetween (ρ (u g)) (τ.action g : τ →L[ℂ] τ)).comp
          (tensorMapBetween (1 : E →L[ℂ] E) T)
    rw [← tensorMapBetween_comp, ← tensorMapBetween_comp]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id, ht]
  exact congrArg (fun f : TensorHilbert E π →L[ℂ] TensorHilbert E τ => f x) he

omit [Nontrivial E] in
theorem tensor_projection_action (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W]
    (g : Γ) (x : TensorHilbert E π) :
    tensorProjection (E := E) W (matchingTuple ρ u π g x) =
      matchingTuple ρ u (π.restrict W hW) g (tensorProjection (E := E) W x) := by
  exact tensor_intertwining (π := π) (τ := π.restrict W hW) ρ u W.orthogonalProjectionOnto
    (fun g x => congrArg (fun f : π →L[ℂ] W => f x) (π.projection_action W hW g)) g x

omit [Nontrivial E] in
theorem tensor_projection_energy (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] [Nontrivial Wᗮ]
    (x : TensorHilbert E π) :
    tupleEnergy S (matchingTuple ρ u π) x =
      tupleEnergy S (matchingTuple ρ u (π.restrict W hW)) (tensorProjection (E := E) W x) +
      tupleEnergy S (matchingTuple ρ u (π.restrict Wᗮ (π.orthogonal_invariant W hW)))
        (tensorProjection (E := E) Wᗮ x) := by
  simp only [tupleEnergy]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [tensorProjection_norm_sq (E := E) W (matchingTuple ρ u π g x - x)]
  simp only [map_sub, tensor_projection_action ρ u π W hW,
    tensor_projection_action ρ u π Wᗮ (π.orthogonal_invariant W hW)]
  rfl

end Intertwine
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InducedApproximation
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v w
section Energies
variable {ι : Type u} {Γ : Type v} {E : ι → Type w}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (l : Filter ι) (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : ∀ i, E i)

theorem energy_tendsto_zero
    (hs : ∀ s ∈ S, Tendsto (fun i => ‖U s i (x i)-x i‖) l (𝓝 0)) :
    Tendsto (fun i => tupleEnergy S (fun g => U g i) (x i)) l (𝓝 0) := by
  have h := tendsto_finsetSum S (fun s h => (hs s h).pow 2)
  simpa [tupleEnergy] using h
end Energies

end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section TensorBounds
variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

theorem tensorMapBetween_norm_le (U : E →L[ℂ] E') (V : F →L[ℂ] F') :
    ‖tensorMapBetween U V‖ ≤ ‖U‖ * ‖V‖ := by
  rw [tensorMapBetween, completed_norm]
  exact TensorProduct.norm_mapL_le _ _

theorem tensorMapBetween_sub_norm_le (U U' : E →L[ℂ] E') (V : F →ₗᵢ[ℂ] F') :
    ‖tensorMapBetween U V.toContinuousLinearMap - tensorMapBetween U' V.toContinuousLinearMap‖
      ≤ ‖U-U'‖ := by
  rw [← tensorMapBetween_sub_left]
  exact (tensorMapBetween_norm_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left V.norm_toContinuousLinearMap_le (norm_nonneg (U-U')))

end TensorBounds
end NuclearUltrapower
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InducedVectors
variable {Γ B E : Type u} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (H : Subgroup Γ) [Fintype (Γ ⧸ H)] (α : FiniteUnitaryRep.{u,u} H)
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

theorem identityCoordinate_comp_inclusion (i : Γ ⧸ H) :
    (identityCoordinate H α).comp (inducedCoordinate H α i).toContinuousLinearMap =
      if i = QuotientGroup.mk 1 then 1 else 0 := by
  classical
  ext v
  change identityCoordinate H α (coordinateInclusion H i v) = (if i = QuotientGroup.mk 1 then (1 : α →L[ℂ] α) else 0) v
  rw [identityCoordinate_inclusion]
  split_ifs <;> rfl

theorem inductionSeed_identity (hu : u 1 = 1) (η : TensorHilbert E α) :
    tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α) (inductionSeed H α ρ u η) = η := by
  classical
  have ht (i : Γ ⧸ H) :
      tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α) (inductionTerm H α ρ u i η) =
        if i = QuotientGroup.mk 1 then η else 0 := by
    change ((tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α)).comp
      (tensorMapBetween (ρ (u (cosetRep H i))) (inducedCoordinate H α i).toContinuousLinearMap)) η = _
    rw [← tensorMapBetween_comp, identityCoordinate_comp_inclusion]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    split_ifs with hi
    · subst i
      rw [cosetRep_identity, hu, Submonoid.coe_one, map_one]
      change tensorMapBetween (1 : E →L[ℂ] E) (1 : α →L[ℂ] α) η = η
      rw [tensorMapBetween_one]
      rfl
    · rw [tensorMapBetween_zero_right]
      rfl
  simp only [inductionSeed, map_sum, ht]
  simp

theorem inductionSeed_norm_ge [Nontrivial E] (hu : u 1 = 1) (η : TensorHilbert E α) :
    ‖η‖ ≤ ‖inductionSeed H α ρ u η‖ := by
  let P := tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α)
  have hp : ‖P‖ ≤ 1 := by
    have h := tensorMapBetween_norm_le (1 : E →L[ℂ] E) (identityCoordinate H α)
    rw [norm_one, one_mul] at h
    exact h.trans (identityCoordinate_norm_le H α)
  have h := P.le_opNorm (inductionSeed H α ρ u η)
  change ‖tensorMapBetween (1 : E →L[ℂ] E) (identityCoordinate H α) (inductionSeed H α ρ u η)‖ ≤ _ at h
  rw [inductionSeed_identity H α ρ u hu] at h
  exact h.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg _))

theorem coordinate_action_comp (g : Γ) (i : Γ ⧸ H) :
    ((finiteInduced H α).action g : finiteInduced H α →L[ℂ] finiteInduced H α).comp
      (inducedCoordinate H α i).toContinuousLinearMap =
    (inducedCoordinate H α (g • i)).toContinuousLinearMap.comp
      (α.action (cosetCocycle H g i) : α →L[ℂ] α) := by
  ext v
  exact coordinateInclusion_action H α.action g i v

omit [CompleteSpace E] in
theorem completedTensorMap_eq_between {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap U V = tensorMapBetween U V := rfl

theorem inductionTerm_action_map (g : Γ) (i : Γ ⧸ H) :
    (matchingTuple ρ u (finiteInduced H α) g :
      TensorHilbert E (finiteInduced H α) →L[ℂ] TensorHilbert E (finiteInduced H α)).comp
      (inductionTerm H α ρ u i) =
      tensorMapBetween (ρ (u g) * ρ (u (cosetRep H i)))
        ((inducedCoordinate H α (g • i)).toContinuousLinearMap.comp
          (α.action (cosetCocycle H g i) : α →L[ℂ] α)) := by
  rw [matchingTuple_toCLM, completedTensorMap_eq_between, inductionTerm,
    ← tensorMapBetween_comp, coordinate_action_comp]
  rfl

theorem inductionTerm_action (g : Γ) (i : Γ ⧸ H) (η : TensorHilbert E α) :
    matchingTuple ρ u (finiteInduced H α) g (inductionTerm H α ρ u i η) =
      tensorMapBetween (ρ (u g) * ρ (u (cosetRep H i)))
        ((inducedCoordinate H α (g • i)).toContinuousLinearMap.comp
          (α.action (cosetCocycle H g i) : α →L[ℂ] α)) η := by
  exact congrArg (fun T : TensorHilbert E α →L[ℂ] TensorHilbert E (finiteInduced H α) => T η)
    (inductionTerm_action_map H α ρ u g i)

end InducedVectors
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_PullbackMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower

section Covariance
variable {E F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Quantitative tensor covariance; the two fixed coordinate maps are isometries. -/
theorem tensor_covariance_bound (U W : E →L[ℂ] E) (V : E →ₗᵢ[ℂ] E)
    (A : F →ₗᵢ[ℂ] F) (J : F →ₗᵢ[ℂ] F') (x : TensorHilbert E F) :
    ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x -
        tensorMapBetween V.toContinuousLinearMap J.toContinuousLinearMap x‖ ≤
      ‖U - V.toContinuousLinearMap * W‖ * ‖x‖ +
        ‖tensorMapBetween W A.toContinuousLinearMap x - x‖ := by
  let T := tensorIsometry V J
  have he : tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap =
      T.toContinuousLinearMap.comp (tensorMapBetween W A.toContinuousLinearMap) := by
    change tensorMapBetween (V.toContinuousLinearMap.comp W)
      (J.toContinuousLinearMap.comp A.toContinuousLinearMap) = _
    exact tensorMapBetween_comp W V.toContinuousLinearMap A.toContinuousLinearMap J.toContinuousLinearMap
  have hd := (tensorMapBetween_sub_norm_le U (V.toContinuousLinearMap * W) (J.comp A))
  have hl := ContinuousLinearMap.le_opNorm
    (tensorMapBetween U (J.comp A).toContinuousLinearMap -
      tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap) x
  have hb := hl.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg x))
  change ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x -
      tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap x‖ ≤ _ at hb
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (tensorMapBetween U (J.comp A).toContinuousLinearMap x)
    (tensorMapBetween (V.toContinuousLinearMap * W) (J.comp A).toContinuousLinearMap x)
    (T x)
  rw [he, ContinuousLinearMap.comp_apply] at ht
  change ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x - T x‖ ≤
    ‖tensorMapBetween U (J.comp A).toContinuousLinearMap x -
      T (tensorMapBetween W A.toContinuousLinearMap x)‖ +
      ‖T (tensorMapBetween W A.toContinuousLinearMap x) - T x‖ at ht
  rw [← map_sub, T.norm_map] at ht
  rw [he, ContinuousLinearMap.comp_apply] at hb
  exact ht.trans (add_le_add hb le_rfl)
end Covariance

section Products
variable {Γ B E : Type*} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

theorem represented_product_defect (g h k l : Γ) (he : g*h=k*l) :
    ‖ρ (u g) * ρ (u h) - ρ (u k) * ρ (u l)‖ ≤
      ‖(u (g*h) : B) - (u g : B)*(u h : B)‖ +
      ‖(u (k*l) : B) - (u k : B)*(u l : B)‖ := by
  rw [← map_mul, ← map_mul, ← map_sub]
  apply (NonUnitalStarAlgHom.norm_apply_le ρ _).trans
  have ht := norm_sub_le_norm_sub_add_norm_sub ((u g : B)*(u h : B))
    (u (g*h) : B) ((u k : B)*(u l : B))
  rw [norm_sub_rev ((u g : B)*(u h : B)) (u (g*h))] at ht
  conv_rhs at ht => rhs; rw [he]
  exact ht
end Products
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
universe u v w
namespace FiniteUnitaryRep
variable {Γ : Type u} {Λ : Type w} [Group Γ] [Group Λ]

theorem Irreducible.comap {π : FiniteUnitaryRep.{u,v} Γ} (hi : π.Irreducible)
    (f : Λ →* Γ) (hf : Function.Surjective f) : (π.comap f).Irreducible := by
  intro W hW
  apply hi W
  intro g x hx
  obtain ⟨h,rfl⟩ := hf g
  exact hW h x hx

end FiniteUnitaryRep
section Range
variable {Γ : Type u} [Group Γ] (θ : Monoid.End Γ) (hθ : Function.Injective θ)

theorem rangeTwist_irreducible {π : FiniteUnitaryRep.{u,u} Γ}
    (hi : π.Irreducible) : (rangeTwist θ hθ π).Irreducible :=
  hi.comap _ (MonoidHom.ofInjective hθ).symm.surjective

theorem rangeTwist_action (π : FiniteUnitaryRep.{u,u} Γ) (g : Γ) :
    (rangeTwist θ hθ π).action ((MonoidHom.ofInjective hθ) g) = π.action g := by
  change π.action ((MonoidHom.ofInjective hθ).symm ((MonoidHom.ofInjective hθ) g)) = π.action g
  rw [MulEquiv.symm_apply_apply]

theorem frobenius_predecessor [Finite (Γ ⧸ θ.range)]
    {π τ : FiniteUnitaryRep.{u,u} Γ} (hi : π.Irreducible)
    (ht : τ.Embeds (finiteInduced θ.range (rangeTwist θ hθ π))) :
    π.Embeds (τ.pull θ) := by
  obtain ⟨T,hT⟩ := frobenius_all_constituents θ.range (rangeTwist θ hθ π)
    (rangeTwist_irreducible θ hθ hi) ht
  refine ⟨T,fun g x => ?_⟩
  have hh := hT ((MonoidHom.ofInjective hθ) g) x
  rw [rangeTwist_action] at hh
  exact hh

end Range
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Shift
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) (t : Δ)

theorem shiftVector_action_map (π : FiniteUnitaryRep.{u,u} Γ) (u : Δ → unitary B) (g : Γ) :
    (matchingTuple ρ (fun h : θ.range => u (f h)) (rangeTwist θ hθ π)
      ((MonoidHom.ofInjective hθ) g) : TensorHilbert E (rangeTwist θ hθ π) →L[ℂ] TensorHilbert E (rangeTwist θ hθ π)).comp
      (shiftVector ρ θ hθ π (u t)).toContinuousLinearMap =
    tensorMapBetween (ρ (u (f (θ g))) * ρ (u t))
      ((rangeTwistInclusion θ hθ π).comp (π.action g).toLinearIsometry).toContinuousLinearMap := by
  rw [matchingTuple_toCLM, completedTensorMap_eq_between, shiftVector, tensorIsometry_toCLM]
  rw [← tensorMapBetween_comp]
  have ha : ((rangeTwist θ hθ π).action ((MonoidHom.ofInjective hθ) g) :
      rangeTwist θ hθ π →L[ℂ] rangeTwist θ hθ π).comp
      (rangeTwistInclusion θ hθ π).toContinuousLinearMap =
      ((rangeTwistInclusion θ hθ π).comp (π.action g).toLinearIsometry).toContinuousLinearMap := by
    ext x
    change (rangeTwist θ hθ π).action ((MonoidHom.ofInjective hθ) g) x = π.action g x
    rw [rangeTwist_action]
    rfl
  rw [ha]
  rfl

theorem shiftVector_displacement (ht : ∀ g, f (θ g) * t = t * f g)
    (π : FiniteUnitaryRep.{u,u} Γ) (u : Δ → unitary B) (g : Γ) (ξ : TensorHilbert E π) :
    ‖matchingTuple ρ (fun h : θ.range => u (f h)) (rangeTwist θ hθ π)
      ((MonoidHom.ofInjective hθ) g) (shiftVector ρ θ hθ π (u t) ξ) -
      shiftVector ρ θ hθ π (u t) ξ‖ ≤
    (‖(u (f (θ g)*t) : B) - (u (f (θ g)) : B)*(u t : B)‖ +
      ‖(u (t*f g) : B) - (u t : B)*(u (f g) : B)‖) * ‖ξ‖ +
      ‖matchingTuple ρ (fun g => u (f g)) π g ξ - ξ‖ := by
  have he := congrArg (fun T : TensorHilbert E π →L[ℂ] TensorHilbert E (rangeTwist θ hθ π) => T ξ)
    (shiftVector_action_map ρ f θ hθ t π u g)
  change matchingTuple ρ (fun h : θ.range => u (f h)) (rangeTwist θ hθ π)
      ((MonoidHom.ofInjective hθ) g) (shiftVector ρ θ hθ π (u t) ξ) = _ at he
  rw [he]
  have hb := tensor_covariance_bound (ρ (u (f (θ g))) * ρ (u t)) (ρ (u (f g)))
    (representedUnitary ρ (u t)).toLinearIsometry (π.action g).toLinearIsometry
    (rangeTwistInclusion θ hθ π) ξ
  have hd := represented_product_defect ρ u (f (θ g)) t t (f g) (ht g)
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_right hd (norm_nonneg ξ)) le_rfl)

end Shift
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section InductionApprox
variable {Γ B E : Type u} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (H : Subgroup Γ) [Fintype (Γ ⧸ H)] (α : FiniteUnitaryRep.{u,u} H)
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

theorem inductionTerm_displacement (g : Γ) (i : Γ ⧸ H) (η : TensorHilbert E α) :
    ‖matchingTuple ρ u (finiteInduced H α) g (inductionTerm H α ρ u i η) -
      inductionTerm H α ρ u (g • i) η‖ ≤
    (‖(u (g*cosetRep H i) : B) - (u g : B)*(u (cosetRep H i) : B)‖ +
      ‖(u (cosetRep H (g • i)*(cosetCocycle H g i : Γ)) : B) -
        (u (cosetRep H (g • i)) : B)*(u (cosetCocycle H g i) : B)‖) * ‖η‖ +
      ‖matchingTuple ρ (fun h : H => u h) α (cosetCocycle H g i) η - η‖ := by
  rw [inductionTerm_action]
  have ht := tensor_covariance_bound
    (ρ (u g) * ρ (u (cosetRep H i))) (ρ (u (cosetCocycle H g i)))
    (representedUnitary ρ (u (cosetRep H (g • i)))).toLinearIsometry
    (α.action (cosetCocycle H g i)).toLinearIsometry (inducedCoordinate H α (g • i)) η
  have hm := represented_product_defect ρ u g (cosetRep H i)
    (cosetRep H (g • i)) (cosetCocycle H g i) (cosetCocycle_factor H g i)
  apply ht.trans
  exact add_le_add (mul_le_mul_of_nonneg_right hm (norm_nonneg η)) le_rfl

theorem inductionSeed_displacement (g : Γ) (η : TensorHilbert E α) :
    ‖matchingTuple ρ u (finiteInduced H α) g (inductionSeed H α ρ u η) -
      inductionSeed H α ρ u η‖ ≤
      ∑ i : Γ ⧸ H, ‖matchingTuple ρ u (finiteInduced H α) g (inductionTerm H α ρ u i η) -
        inductionTerm H α ρ u (g • i) η‖ := by
  classical
  have he : (∑ i : Γ ⧸ H, inductionTerm H α ρ u (g • i) η) = inductionSeed H α ρ u η := by
    exact Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm (Γ ⧸ H)) (fun i => inductionTerm H α ρ u i η)
  change (∑ i : Γ ⧸ H, inductionTerm H α ρ u (g • i) η) = ∑ i : Γ ⧸ H, inductionTerm H α ρ u i η at he
  rw [inductionSeed, map_sum, ← he, ← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

end InductionApprox

section Limits
variable {Γ B E : Type u} [Group Γ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (H : Subgroup Γ) [Fintype (Γ ⧸ H)] (α : ℕ → FiniteUnitaryRep.{u,u} H)
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → ℕ → unitary B)
  (ω : Ultrafilter ℕ) (η : ∀ n, TensorHilbert E (α n))

theorem inductionSeed_almostInvariant
    (hη : ∀ n, ‖η n‖ = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (hinv : ∀ h : H, Tendsto (fun n =>
      ‖matchingTuple ρ (fun h : H => u h n) (α n) h (η n) - η n‖)
        (ω : Filter ℕ) (𝓝 0)) (g : Γ) :
    Tendsto (fun n => ‖matchingTuple ρ (fun g => u g n) (finiteInduced H (α n)) g
      (inductionSeed H (α n) ρ (fun g => u g n) (η n)) -
        inductionSeed H (α n) ρ (fun g => u g n) (η n)‖) (ω : Filter ℕ) (𝓝 0) := by
  have hi (i : Γ ⧸ H) : Tendsto (fun n =>
      ‖matchingTuple ρ (fun g => u g n) (finiteInduced H (α n)) g
        (inductionTerm H (α n) ρ (fun g => u g n) i (η n)) -
        inductionTerm H (α n) ρ (fun g => u g n) (g • i) (η n)‖)
        (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (inductionTerm_displacement H (α n) ρ (fun g => u g n) g i (η n)))
    simp_rw [hη, mul_one]
    simpa only [add_zero] using ((hmul g (cosetRep H i)).add
      (hmul (cosetRep H (g • i)) (cosetCocycle H g i)) |>.add (hinv (cosetCocycle H g i)))
  apply squeeze_zero (fun n => norm_nonneg _) (fun n =>
    inductionSeed_displacement H (α n) ρ (fun g => u g n) g (η n))
  simpa using tendsto_finsetSum Finset.univ (fun i _ => hi i)
end Limits
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

omit [Nontrivial E] in
theorem Matches.exists_irreducible {a : ℝ} (π : FiniteUnitaryRep.{u,v} Γ)
    (hm : Matches ρ S u a π) :
    ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ τ.Embeds π ∧ Matches ρ S u a τ := by
  classical
  suffices hall : ∀ n : ℕ, ∀ π : FiniteUnitaryRep.{u,v} Γ,
      Module.finrank ℂ π = n → Matches ρ S u a π →
      ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ τ.Embeds π ∧ Matches ρ S u a τ by
    exact hall _ π rfl hm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro π hn hm
    by_cases hi : π.Irreducible
    · exact ⟨π,hi,FiniteUnitaryRep.embeds_refl π,hm⟩
    unfold FiniteUnitaryRep.Irreducible at hi
    push Not at hi
    obtain ⟨W,hW,hWb,hWt⟩ := hi
    let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWb
    let : Nontrivial Wᗮ := Submodule.nontrivial_iff_ne_bot.mpr
      (mt W.orthogonal_eq_bot_iff.mp hWt)
    have hd := W.finrank_add_finrank_orthogonal
    have hp1 : 0 < Module.finrank ℂ W := Module.finrank_pos
    have hp2 : 0 < Module.finrank ℂ Wᗮ := Module.finrank_pos
    have hwlt : Module.finrank ℂ (π.restrict W hW) < n := by
      change Module.finrank ℂ W < n
      omega
    have hplt : Module.finrank ℂ (π.restrict Wᗮ (π.orthogonal_invariant W hW)) < n := by
      change Module.finrank ℂ Wᗮ < n
      omega
    obtain ⟨x,hx⟩ := (matches_iff_homogeneous ρ S u a π).mp hm
    have he := tensor_projection_energy ρ S u π W hW x
    have hn' := tensorProjection_norm_sq (E := E) W x
    have hor :
        tupleEnergy S (matchingTuple ρ u (π.restrict W hW)) (tensorProjection (E := E) W x) <
          a * ‖tensorProjection (E := E) W x‖^2 ∨
        tupleEnergy S (matchingTuple ρ u (π.restrict Wᗮ (π.orthogonal_invariant W hW)))
          (tensorProjection (E := E) Wᗮ x) < a * ‖tensorProjection (E := E) Wᗮ x‖^2 := by
      rw [he, hn', mul_add] at hx
      exact lt_or_lt_of_add_lt_add hx
    rcases hor with hleft | hright
    · have hmW := (matches_iff_homogeneous ρ S u a (π.restrict W hW)).mpr ⟨_,hleft⟩
      obtain ⟨τ,hτ,hU,hmτ⟩ := ih _ hwlt (π.restrict W hW) rfl hmW
      exact ⟨τ,hτ,hU.trans (π.restrict_embeds W hW),hmτ⟩
    · have hmW := (matches_iff_homogeneous ρ S u a
        (π.restrict Wᗮ (π.orthogonal_invariant W hW))).mpr ⟨_,hright⟩
      obtain ⟨τ,hτ,hU,hmτ⟩ := ih _ hplt (π.restrict Wᗮ (π.orthogonal_invariant W hW)) rfl hmW
      exact ⟨τ,hτ,hU.trans (π.restrict_embeds Wᗮ (π.orthogonal_invariant W hW)),hmτ⟩

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Predecessors
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Predecessors
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)] (t : Δ)
  (S : Finset Γ) (u : Δ → ℕ → unitary B) (ω : Ultrafilter ℕ)

include hθ in
theorem sequence_predecessors (κ a : ℝ) (hgap : HasKazhdanGap.{u,u} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ) (ha0 : 0 < a)
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π : ℕ → FiniteUnitaryRep.{u,u} Γ) (hirr : ∀ n, (π n).Irreducible)
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u (f g) n) a (π n)) :
    ∀ᶠ n in (ω : Filter ℕ), ∃ τ : FiniteUnitaryRep.{u,u} Γ,
      τ.Irreducible ∧ Matches ρ S (fun g => u (f g) n) a τ ∧ (π n).Embeds (τ.pull θ) := by
  classical
  let : Fintype (Γ ⧸ θ.range) := Fintype.ofFinite _
  have hu1 (n : ℕ) : u (f 1) n = 1 := by rw [map_one,h1]
  have humul (g h : Γ) : Tendsto
      (fun n => ‖(u (f (g*h)) n : B) - (u (f g) n : B)*(u (f h) n : B)‖)
      (ω : Filter ℕ) (𝓝 0) := by simpa only [map_mul] using hmul (f g) (f h)
  obtain ⟨ξ,hξ,hξinv⟩ := matched_vectors ρ S (fun g => u (f g)) π ω κ a hgap hS ha hω hu1 humul hm
  let α := fun n => rangeTwist θ hθ (π n)
  let η : ∀ n, TensorHilbert E (α n) := fun n => shiftVector ρ θ hθ (π n) (u t n) (ξ n)
  have hη (n : ℕ) : ‖η n‖ = 1 := by rw [LinearIsometry.norm_map,hξ]
  have hηinv (h : θ.range) : Tendsto
      (fun n => ‖matchingTuple ρ (fun h : θ.range => u (f h) n) (α n) h (η n) - η n‖)
      (ω : Filter ℕ) (𝓝 0) := by
    obtain ⟨g,rfl⟩ := (MonoidHom.ofInjective hθ).surjective h
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => shiftVector_displacement ρ f θ hθ t ht (π n) (fun g => u g n) g (ξ n))
    simp_rw [hξ,mul_one]
    simpa only [add_zero] using ((hmul (f (θ g)) t).add (hmul t (f g)) |>.add (hξinv g))
  let y := fun n => inductionSeed θ.range (α n) ρ (fun g => u (f g) n) (η n)
  have hy (n : ℕ) : 1 ≤ ‖y n‖ := by
    have hb := inductionSeed_norm_ge θ.range (α n) ρ (fun g => u (f g) n) (hu1 n) (η n)
    rw [hη] at hb
    exact hb
  have he : Tendsto (fun n => tupleEnergy S
      (matchingTuple ρ (fun g => u (f g) n) (finiteInduced θ.range (α n))) (y n))
      (ω : Filter ℕ) (𝓝 0) := by
    apply energy_tendsto_zero (ω : Filter ℕ) S
      (fun g n => matchingTuple ρ (fun g => u (f g) n) (finiteInduced θ.range (α n)) g) y
    intro s _
    exact inductionSeed_almostInvariant θ.range α ρ (fun g => u (f g)) ω η hη humul hηinv s
  have hea : ∀ᶠ n in (ω : Filter ℕ), tupleEnergy S
      (matchingTuple ρ (fun g => u (f g) n) (finiteInduced θ.range (α n))) (y n) < a :=
    (tendsto_order.mp he).2 a ha0
  filter_upwards [hea] with n hn
  have hmI : Matches ρ S (fun g => u (f g) n) a (finiteInduced θ.range (α n)) := by
    apply (matches_iff_homogeneous ρ S (fun g => u (f g) n) a _).mpr
    refine ⟨y n, hn.trans_le ?_⟩
    have hn2 : 1 ≤ ‖y n‖^2 := by nlinarith [hy n]
    nlinarith
  obtain ⟨τ,hτ,htau,hmtau⟩ := Matches.exists_irreducible ρ S (fun g => u (f g) n) _ hmI
  exact ⟨τ,hτ,hmtau,frobenius_predecessor θ hθ (hirr n) htau⟩

end Predecessors
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Predecessors
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)] (t : Δ)
  (S : Finset Γ) (u : Δ → ℕ → unitary B) (ω : Ultrafilter ℕ)

include hθ in
/-- Uniformity is extracted by selecting a bad representation at every bad
coordinate. The selected dimensions are not bounded. -/
theorem uniform_predecessors_oai (κ a : ℝ) (hgap : HasKazhdanGap.{u,u} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ) (ha0 : 0 < a)
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π₀ : FiniteUnitaryRep.{u,u} Γ) (hirr₀ : π₀.Irreducible) :
    ∀ᶠ n in (ω : Filter ℕ), ∀ π : FiniteUnitaryRep.{u,u} Γ,
      π.Irreducible → Matches ρ S (fun g => u (f g) n) a π →
      ∃ τ : FiniteUnitaryRep.{u,u} Γ, τ.Irreducible ∧
        Matches ρ S (fun g => u (f g) n) a τ ∧ π.Embeds (τ.pull θ) := by
  classical
  by_contra h
  have hb := (ω.eventually_not).mpr h
  simp only [not_forall] at hb
  let bad (n : ℕ) (π : FiniteUnitaryRep.{u,u} Γ) : Prop := π.Irreducible ∧
    Matches ρ S (fun g => u (f g) n) a π ∧
    ¬ ∃ τ : FiniteUnitaryRep.{u,u} Γ, τ.Irreducible ∧
      Matches ρ S (fun g => u (f g) n) a τ ∧ π.Embeds (τ.pull θ)
  have hb' : ∀ᶠ n in (ω : Filter ℕ), ∃ π, bad n π := hb.mono fun n hn => by
    obtain ⟨π, hi, hm, hn⟩ := hn
    exact ⟨π, hi, hm, hn⟩
  let π : ℕ → FiniteUnitaryRep.{u,u} Γ := fun n =>
    if hn : ∃ π, bad n π then hn.choose else π₀
  have hirr (n : ℕ) : (π n).Irreducible := by
    dsimp only [π]
    split_ifs with hn
    · exact hn.choose_spec.1
    · exact hirr₀
  have hs : ∀ᶠ n in (ω : Filter ℕ), bad n (π n) := hb'.mono fun n hn => by
    dsimp only [π]
    rw [dite_eq_left hn]
    exact hn.choose_spec
  have hm := hs.mono fun _ hn => hn.2.1
  have hp := sequence_predecessors ρ f θ hθ t S u ω κ a hgap hS ha ha0 ht hω h1 hmul π hirr hm
  obtain ⟨n,hn,hpn⟩ := (hs.and hp).exists
  exact hn.2.2 hpn

end Predecessors
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.NuclearUltrapower.uniform_predecessors_oai.{u} := @OAI.NuclearUltrapower.uniform_predecessors_oai.{u}
