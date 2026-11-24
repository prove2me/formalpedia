-- Prove2me | solution 1 for GlobalTheory.SignedLengthLogDet.relLength_span_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:04.158429+00:00
-- url     : https://prove2.me/submissions/8b6ded41-2f30-4443-9a83-da811c238d08

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthLogDet_length_coker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module
namespace GlobalTheory.SignedLengthLogDet
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Submodule R V} (a : Basis ι R A) (h : Matrix ι ι R) (hh : h.det ≠ 0) (v : ι → V)
    (hv : ∀ j, v j = ∑ i, h i j • (a i : V)) :
    Submodule.span R (Set.range v) ≤ A ∧
      relLength A (Submodule.span R (Set.range v)) = Ring.ord R h.det := by
  let φ : A →ₗ[R] A := Matrix.toLin a a h
  have hφ : ∀ j, (φ (a j) : V) = v j := by
    intro j
    rw [hv j]
    simp [φ, Matrix.toLin_self]
  have hdet : LinearMap.det φ = h.det := LinearMap.det_toLin a h
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : h.mulVec (a.repr x) = 0 := by
      rw [← Matrix.repr_toLin a a h x]
      change ⇑(a.repr (φ x)) = 0
      rw [hx]
      simp
    have := Matrix.eq_zero_of_mulVec_eq_zero hh h0
    apply a.repr.injective
    ext i
    simpa using congrFun this i
  have hmap : (LinearMap.range φ).map A.subtype = Submodule.span R (Set.range v) := by
    rw [← Submodule.map_top, ← a.span_eq, Submodule.map_span, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp]
    congr 2
    funext j
    exact hφ j
  refine ⟨hmap ▸ Submodule.map_subtype_le _ _, ?_⟩
  have hsub : (Submodule.span R (Set.range v)).submoduleOf A = LinearMap.range φ := by
    rw [← hmap]
    exact Submodule.comap_map_eq_of_injective A.injective_subtype _
  rw [relLength_def, hsub, length_coker a φ hinj, hdet]
end GlobalTheory.SignedLengthLogDet
