-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.exists_of_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:28.087392+00:00
-- url     : https://prove2.me/submissions/5c80e689-e1fb-4204-8342-dadaf1f96888

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.SelfDualLatticeCompare
theorem _root_.solution (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
  · have : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := he
    rw [h0, Algebra.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
    have hx' : σ x = x := hx
    have := h.2.2.2 τ x
    rw [hx'] at this
    exact this.symm
end GlobalTheory.SelfDualLatticeCompare
