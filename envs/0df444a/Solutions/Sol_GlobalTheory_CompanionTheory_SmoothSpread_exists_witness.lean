-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothSpread.exists_witness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:39:43.621494+00:00
-- url     : https://prove2.me/submissions/9c0119b5-3010-4e5f-a82a-fe5ec4ba9a4a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread
variable {T S ι σ : Type} [CommRing T] [CommRing S] [Algebra T S]
namespace GlobalTheory.CompanionTheory.SmoothSpread
theorem _root_.solution [Algebra.FormallySmooth T S] (Q : Algebra.Presentation T S ι σ) :
    ∃ h : ι → Q.Ring, (∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation)) ∧
      ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2 := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  obtain ⟨(τ : S →ₐ[T] MvPolynomial _ T ⧸ RingHom.ker f ^ 2), hsig⟩ :=
    (Algebra.FormallySmooth.iff_split_surjection f Q.algebraMap_surjective).mp inferInstance
  have hex (i : _) := Ideal.Quotient.mk_surjective (τ <| Q.val i)
  choose h hh using hex
  have hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = τ.comp (aeval Q.val) :=
    algHom_ext (by simp [hh])
  refine ⟨h, fun i ↦ ?_, fun j ↦ ?_⟩
  · have hs : f (h i) = Q.val i := by
      rw [← AlgHom.kerSquareLift_mk]
      exact hh i ▸ congr($hsig (Q.val i))
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero, hs]
    simp [f]
  · have ho : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (Q.relation j)) = 0 := by
      suffices ho : τ (aeval Q.val (Q.relation j)) = 0 by
        convert! ho
        exact congr($hdiag _)
      simp
    rwa [Ideal.Quotient.eq_zero_iff_mem, hkerf] at ho
end GlobalTheory.CompanionTheory.SmoothSpread
