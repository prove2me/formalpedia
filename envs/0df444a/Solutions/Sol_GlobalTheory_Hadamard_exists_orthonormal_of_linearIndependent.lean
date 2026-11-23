-- Prove2me | solution 1 for GlobalTheory.Hadamard.exists_orthonormal_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:00.960228+00:00
-- url     : https://prove2.me/submissions/3db1f8f3-6b48-472f-b6ee-2186372a8898

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.Hadamard
theorem _root_.solution {x : ι → E} (hx : LinearIndependent 𝕜 x) :
    ∃ (e : ι → E) (m : Matrix ι ι 𝕜), Orthonormal 𝕜 e ∧ ∀ j, x j = ∑ i, m i j • e i := by
  set S := Submodule.span 𝕜 (Set.range x)
  haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range x)
  have h : finrank 𝕜 S = Fintype.card ι := finrank_span_eq_card hx
  let b : OrthonormalBasis ι 𝕜 S :=
    (stdOrthonormalBasis 𝕜 S).reindex (Fintype.equivFinOfCardEq h.symm).symm
  let y : ι → S := fun j => ⟨x j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨fun i => (b i : E), of fun i j => b.repr (y j) i,
    b.orthonormal.comp_linearIsometry S.subtypeₗᵢ, fun j => ?_⟩
  have := congrArg (fun s : S => (s : E)) (b.sum_repr (y j))
  simpa using this.symm
end GlobalTheory.Hadamard
