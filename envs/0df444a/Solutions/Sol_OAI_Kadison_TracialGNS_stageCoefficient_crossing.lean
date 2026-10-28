-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.stageCoefficient_crossing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:47:59.127304+00:00
-- url     : https://prove2.me/submissions/f3ba9335-b4a3-4483-b738-49489edcc31d

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_SchurWeyl_centered_expansion_contractions
import Theorems.Thm_OAI_Kadison_TracialGNS_stageCoefficient_cycleCutoff
import Theorems.Thm_OAI_Kadison_TracialGNS_stage_pairing_expansion
import Theorems.Thm_OAI_Kadison_TracialGNS_stage_pairing_same_side_zero

section
-- module Solutions.OAIQ039_CM.Commutator_CrossingPairings
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

namespace Kadison

namespace Pairing

theorem contraction_crossPairing {k l : ℕ} {E : Type*} (e : Fin k ≃ Fin l)
    (B : E → E → ℂ) (v : TailSlots k l → E) :
    contraction (crossPairing e) B v = ∏ a, B (v (.inl a)) (v (.inr (e a))) := by
  classical
  rw [contraction, Finset.prod_filter]
  erw [Fintype.prod_sum_type]
  simp only [crossPairing_inl, crossPairing_inr]
  change (∏ a : Fin k, if (toLex (.inl a) : TailSlots k l) < toLex (.inr (e a))
      then B (v (toLex (.inl a))) (v (toLex (.inr (e a)))) else 1) *
    (∏ b : Fin l, if (toLex (.inr b) : TailSlots k l) < toLex (.inl (e.symm b))
      then B (v (toLex (.inr b))) (v (toLex (.inl (e.symm b)))) else 1) = _
  simp
  rfl

theorem sum_contraction_crossing {k l : ℕ} {E : Type*}
    (B : E → E → ℂ) (v : TailSlots k l → E) (c : Pairing (TailSlots k l) → ℂ)
    (hz : ∀ τ, ¬ Crosses τ → c τ = 0) :
    (∑ τ, c τ * contraction τ B v) =
      ∑ e : Fin k ≃ Fin l, c (crossPairing e) * ∏ a, B (v (.inl a)) (v (.inr (e a))) := by
  classical
  calc
    _ = ∑ τ ∈ Finset.univ.filter Crosses, c τ * contraction τ B v := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro τ _ hτ
      rw [hz τ (by simpa using hτ), zero_mul]
    _ = ∑ τ : {τ : Pairing (TailSlots k l) // Crosses τ},
        c τ.val * contraction τ.val B v := by
      exact Finset.sum_subtype (F := inferInstance) _ (by intro τ; simp) _
    _ = ∑ e : Fin k ≃ Fin l, c (crossPairing e) * contraction (crossPairing e) B v := by
      exact (Equiv.sum_comp (crossingEquiv k l) _).symm
    _ = _ := by simp_rw [contraction_crossPairing]

end Pairing

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry3
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

namespace Kadison.Pairing

lemma not_crosses_iff_same_side {k l : ℕ} (σ : Pairing (TailSlots k l)) :
    ¬ Crosses σ ↔ (∃ a b : Fin k, σ (.inl a) = .inl b) ∨
      (∃ a b : Fin l, σ (.inr a) = .inr b) := by
  constructor
  · intro hn
    by_contra h
    apply hn
    constructor
    · intro a
      cases he : σ (.inl a) with
      | inl b => exact (h (Or.inl ⟨a, b, he⟩)).elim
      | inr b => exact ⟨b, rfl⟩
    · intro a
      cases he : σ (.inr a) with
      | inl b => exact ⟨b, rfl⟩
      | inr b => exact (h (Or.inr ⟨a, b, he⟩)).elim
  · rintro (⟨a, b, he⟩ | ⟨a, b, he⟩) hc
    · obtain ⟨j, hj⟩ := hc.1 a
      rw [he] at hj
      cases hj
    · obtain ⟨j, hj⟩ := hc.2 a
      rw [he] at hj
      cases hj

end Kadison.Pairing
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry4
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

variable {k l : ℕ} (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include h1 in
theorem stageCoefficient_crossing_oai (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c : (Fin k ≃ Fin l) → ℂ, ∀ n (a : Matrix (I n) (I n) ℂ)
      (v : TailSlots k l → Matrix (I n) (I n) ℂ), (∀ j, Matrix.trace (v j) = 0) →
      stageCoefficient τ Y (φ n) (fun o => o.elim a v) =
        ((Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace a) *
          ∑ b : Fin k ≃ Fin l, c b * ∏ i,
            ((Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (v (.inl i) * v (.inr (b i)))) := by
  classical
  obtain ⟨d₀, hexp₀, hd₀⟩ := stageCoefficient_cycleCutoff τ hτ h1 Y I φ e he hsize hY hleft
  let d : Equiv.Perm (Option (TailSlots k l)) → ℂ := d₀
  have hexp (n) (v : Option (TailSlots k l) → Matrix (I n) (I n) ℂ) :
      stageCoefficient τ Y (φ n) v = ∑ σ, d σ * SchurWeyl.cycleTrace σ v := hexp₀ n v
  have hd (σ : Equiv.Perm (Option (TailSlots k l)))
      (hσ : 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (TailSlots k l)) + 1) :
      d σ = 0 := hd₀ σ hσ
  let c : Pairing (TailSlots k l) → ℂ := fun σ => d (SchurWeyl.endpointPairingPerm σ)
  have hc (n) (v : TailSlots k l → Matrix (I n) (I n) ℂ) (hv : ∀ j, (v j).trace = 0) :
      stageCoefficient τ Y (φ n) (fun o => o.elim (1 : Matrix (I n) (I n) ℂ) v) =
        ∑ σ, c σ * Pairing.contraction σ
          (fun X Z => (Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v :=
    stage_pairing_expansion τ Y (φ n) d hd (hexp n) v hv
  have hz (σ : Pairing (TailSlots k l)) (hσ : ¬ σ.Crosses) : c σ = 0 :=
    stage_pairing_same_side_zero τ hτ h1 Y I φ
      (fun q => let ⟨m, hm⟩ := hsize 0 q; ⟨m, hm.2⟩) c hc σ
      ((Pairing.not_crosses_iff_same_side σ).mp hσ)
  refine ⟨fun b => c (Pairing.crossPairing b), ?_⟩
  intro n a v hv
  have hh := SchurWeyl.centered_expansion_contractions d hd
    (fun o : Option (TailSlots k l) => o.elim a v) (fun j => hv j)
  have hs := Pairing.sum_contraction_crossing
    (fun X Z : Matrix (I n) (I n) ℂ => (Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v c hz
  have hh' : (∑ σ, d σ * SchurWeyl.cycleTrace σ (fun o : Option (TailSlots k l) => o.elim a v)) =
      ((Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace a) *
        ∑ σ, c σ * Pairing.contraction σ
          (fun X Z => (Fintype.card (I n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v := hh
  rw [hs] at hh'
  exact (hexp n (fun o : Option (TailSlots k l) => o.elim a v)).trans hh'

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialGNS.stageCoefficient_crossing_oai.{u_1} := @OAI.Kadison.TracialGNS.stageCoefficient_crossing_oai.{u_1}
