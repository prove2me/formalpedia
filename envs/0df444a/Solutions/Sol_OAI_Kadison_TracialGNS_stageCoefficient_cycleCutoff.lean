-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:22.087103+00:00
-- url     : https://prove2.me/submissions/84803095-f6e3-424a-ab17-683f17f29f60

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_SchurWeyl_endpoint_coefficients_vanish_of_rank_one
import Theorems.Thm_OAI_Kadison_SchurWeyl_matrix_union_expansion
import Theorems.Thm_OAI_Kadison_TracialGNS_stageCoefficient_rank_one

section
-- module Solutions.OAIQ039_CM.Commutator_CenteredSpace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma coe_center (Ω : E) (hΩ : ‖Ω‖ = 1) (x : E) :
    (center Ω x : E) = x - inner ℂ Ω x • Ω := by
  change (ℂ ∙ Ω)ᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℂ hΩ]

lemma center_isometry (Ω : E) (hΩ : ‖Ω‖ = 1) (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω)
    (x : E) : U (center Ω x : E) = (center Ω (U x) : E) := by
  rw [coe_center Ω hΩ, coe_center Ω hΩ, map_sub, map_smul, hU]
  congr 2
  have h := U.inner_map_map Ω x
  rw [hU] at h
  exact h.symm

lemma centeredIsometry_center (Ω : E) (hΩ : ‖Ω‖ = 1)
    (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω) (x : E) :
    centeredIsometry Ω U hU (center Ω x) = center Ω (U x) := by
  apply Subtype.ext
  exact center_isometry Ω hΩ U hU x

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

omit [Nonempty I] in
lemma stage_conjugation (u : unitary (Matrix I I ℂ)) (a : Matrix I I ℂ) :
    conjugation τ hτ (stageUnitary φ u) (stageVector τ φ a) =
      stageVector τ φ ((u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ)) := by
  change conjugation τ hτ (stageUnitary φ u)
    (τ.toPreGNS (φ a) : τ.GNS) = (_ : τ.GNS)
  rw [conjugation_coe]
  change (τ.toPreGNS ((φ (u : Matrix I I ℂ)) * φ a * star (φ (u : Matrix I I ℂ))) : τ.GNS) =
    (τ.toPreGNS (φ ((u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ))) : τ.GNS)
  simp only [map_mul, map_star]

omit [Nonempty I] in
include h1 in
lemma centered_stage_conjugation (u : unitary (Matrix I I ℂ)) (a : Matrix I I ℂ) :
    centeredIsometry (vacuum τ) (conjugation τ hτ (stageUnitary φ u))
      (conjugation_vacuum τ hτ _) (centeredStageVector τ φ a) =
      centeredStageVector τ φ ((u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ)) := by
  change centeredIsometry _ _ _ (center _ (stageVector τ φ a)) = _
  rw [centeredIsometry_center _ (vacuum_norm τ h1), stage_conjugation]
  rfl

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorActions
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

open UniformSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

open PreHilbert

variable (E F : PreHilbert) (k l : ℕ)

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [StarAddMonoid M]

lemma coefficient_invariant
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F)
    (U : E →ₗᵢ[ℂ] E) (V : F →ₗᵢ[ℂ] F) (C : M → M)
    (hstar : ∀ a, star (C a) = C (star a))
    (hv₀ : ∀ a, v₀ (C a) = U (v₀ a)) (hv₁ : ∀ a, v₁ (C a) = V (v₁ a))
    (hΩ : U Ω = Ω)
    (hY : Y.comp (wordMap E F U V k).toContinuousLinearMap =
      (wordMap E F U V l).toContinuousLinearMap.comp Y)
    (A : Option (Fin k ⊕ Fin l) → M) :
    coefficient E F k l Y Ω v₀ v₁ (fun i => C (A i)) =
      coefficient E F k l Y Ω v₀ v₁ A := by
  have hy (x : wordSpace E F k) :
      Y (wordMap E F U V k x) = wordMap E F U V l (Y x) :=
    congrArg (fun T : wordSpace E F k →L[ℂ] wordSpace E F l => T x) hY
  simp only [coefficient, hstar, hv₀, hv₁]
  rw [← wordMap_word]
  have hx : word E F k Ω (fun i => V (v₁ (A (some (.inl i))))) =
      wordMap E F U V k (word E F k Ω (fun i => v₁ (A (some (.inl i))))) := by
    rw [wordMap_word, hΩ]
  rw [hx, hy, LinearIsometry.inner_map_map]

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in
include h1 in
lemma stageCoefficient_invariant (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (u : unitary (Matrix I I ℂ))
    (hY : Y.comp (wordConjugation τ hτ (stageUnitary φ u) k).toContinuousLinearMap =
      (wordConjugation τ hτ (stageUnitary φ u) l).toContinuousLinearMap.comp Y)
    (v : Option (Fin k ⊕ Fin l) → Matrix I I ℂ) :
    stageCoefficient τ Y φ (fun i => (u : Matrix I I ℂ) * v i * star (u : Matrix I I ℂ)) =
      stageCoefficient τ Y φ v := by
  apply coefficient_invariant (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
    (stageVector τ φ) (centeredStageVector τ φ) (conjugation τ hτ (stageUnitary φ u))
    (centeredIsometry (vacuum τ) (conjugation τ hτ (stageUnitary φ u))
      (conjugation_vacuum τ hτ _)) (fun a => (u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ))
  · intro a
    simp only [star_mul, star_star, mul_assoc]
  · intro a
    exact (stage_conjugation τ hτ φ u a).symm
  · intro a
    exact (centered_stage_conjugation τ hτ h1 φ u a).symm
  · exact conjugation_vacuum τ hτ _
  · exact hY

variable {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]

omit [Nonempty I] [Nonempty K] in
lemma stageCoefficient_compatible (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (ψ : Matrix K K ℂ →⋆ₐ[ℂ] A) (e : Matrix I I ℂ →⋆ₐ[ℂ] Matrix K K ℂ)
    (he : ∀ a, ψ (e a) = φ a) (v : Option (Fin k ⊕ Fin l) → Matrix I I ℂ) :
    stageCoefficient τ Y ψ (fun i => e (v i)) = stageCoefficient τ Y φ v := by
  change coefficient (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
    (stageVector τ ψ) (centeredStageVector τ ψ) (fun i => e (v i)) =
    coefficient (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
      (stageVector τ φ) (centeredStageVector τ φ) v
  simp only [coefficient, stageVector, centeredStageVector, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, map_star, he]

include h1 in
theorem stageCoefficient_expansion (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y) :
    ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
      ∀ n (v : Option (Fin k ⊕ Fin l) → Matrix (I n) (I n) ℂ),
        stageCoefficient τ Y (φ n) v = ∑ σ, c σ * SchurWeyl.cycleTrace σ v := by
  apply SchurWeyl.matrix_union_expansion I (fun h => (e h).toAlgHom) hsize
    (fun n => stageCoefficient τ Y (φ n))
  · intro n u v
    exact stageCoefficient_invariant τ hτ h1 Y (φ n) u (hY n u) v
  · intro n m h v
    exact stageCoefficient_compatible τ Y (φ n) (φ m) (e h) (he n m h) v

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include h1 in
theorem stageCoefficient_cycleCutoff_oai (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
      (∀ n (v : Option (Fin k ⊕ Fin l) → Matrix (I n) (I n) ℂ),
        stageCoefficient τ Y (φ n) v = ∑ σ, c σ * SchurWeyl.cycleTrace σ v) ∧
      ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (Fin k ⊕ Fin l)) + 1 → c σ = 0 := by
  classical
  obtain ⟨c, hc⟩ := stageCoefficient_expansion τ hτ h1 Y I φ e he hsize hY
  refine ⟨c, hc, ?_⟩
  intro σ hσ
  let J := Option (Fin k ⊕ Fin l)
  choose j hj using fun n => hsize 0 (max n (Fintype.card J))
  have hjJ (n) : Fintype.card J ≤ Fintype.card (I (j n)) :=
    (le_max_right n (Fintype.card J)).trans (hj n).2
  let b (n) : J ↪ I (j n) := Classical.choice (Function.Embedding.nonempty_of_card_le (hjJ n))
  apply SchurWeyl.endpoint_coefficients_vanish_of_rank_one (fun n => I (j n))
    (none : J) (fun n => b n) (fun n => (b n).injective)
    (fun n => stageCoefficient τ Y (φ (j n))) c ‖Y‖ (ContinuousLinearMap.opNorm_nonneg Y) (fun n => hc (j n))
  · intro n ρ
    exact stageCoefficient_rank_one τ hτ h1 Y (φ (j n)) hleft (b n) ρ
  · intro B
    exact ⟨B, (le_max_left B (Fintype.card J)).trans (hj B).2⟩
  · exact hσ

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff_oai.{u_1} := @OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff_oai.{u_1}
