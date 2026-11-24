-- Prove2me | solution 1 for GlobalTheory.UnramConjUnit.conj_ne_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:07:26.513579+00:00
-- url     : https://prove2.me/submissions/742e880a-e547-4350-8131-5af5fc9eda28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal GlobalTheory.SelfDualLatticeCompare
open GlobalTheory GlobalTheory.UnramConjUnit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.UnramConjUnit
namespace _root_.GlobalTheory.UnramConjUnit
theorem _root_.solution (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ¬ ∀ e, σ e = e := by
  intro hσ
  obtain ⟨-, hE, -, hconj⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := hE.isComplex w
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  ext x
  simpa [hσ x] using (hconj w.embedding x).symm
end _root_.GlobalTheory.UnramConjUnit
end GlobalTheory.UnramConjUnit
