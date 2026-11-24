-- Prove2me | solution 1 for GlobalTheory.EmbUnitBallConj.exists_equiv_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:44.660439+00:00
-- url     : https://prove2.me/submissions/786c9fdf-246f-4901-a236-0a5ace41ca41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicEmbeddingsConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbUnitBallConj
variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]
namespace GlobalTheory.EmbUnitBallConj
theorem _root_.solution {F T K : Type} [Field F] [CommRing T] [Algebra F T] [Field K]
    [Algebra F K] [IsAlgClosed K] [Algebra.IsAlgebraic F K] (f g : T →ₐ[F] K)
    (h : RingHom.ker f ≤ RingHom.ker g) : ∃ σ : K ≃ₐ[F] K, ∀ x, σ (f x) = g x := by
  let S : IntermediateField F K :=
    Subalgebra.IsAlgebraic.toIntermediateField (S := f.range)
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
  let φ : f.range →ₐ[F] K :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)).comp
      (Ideal.quotientKerEquivRange f).symm.toAlgHom
  have hφ : ∀ x, φ ⟨f x, x, rfl⟩ = g x := by
    intro x
    have : (Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩ = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)
      ((Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩) = g x
    rw [this]
    rfl
  let φ' : S →ₐ[F] K := φ
  obtain ⟨ψ, hψ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := F) (L := S) (M := K)
    (E := K) φ'
  refine ⟨AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ), fun x => ?_⟩
  rw [← hφ x]
  exact DFunLike.congr_fun hψ (⟨f x, x, rfl⟩ : S)
end GlobalTheory.EmbUnitBallConj
