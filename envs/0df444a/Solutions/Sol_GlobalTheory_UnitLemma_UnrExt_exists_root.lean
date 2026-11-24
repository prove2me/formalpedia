-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrExt.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:45.654071+00:00
-- url     : https://prove2.me/submissions/acb6d978-f47c-42df-a740-209ce73aaaf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_isUnit_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrExt
variable {W k : Type} [CommRing W] [IsLocalRing W] [Field k] (v : W →+* k)
  (hker : RingHom.ker v = maximalIdeal W)
include hker
namespace GlobalTheory.UnitLemma.UnrExt
theorem _root_.solution [IsAdicComplete (maximalIdeal W) W] (hv : Function.Surjective v) (f : W[X]) (hf : f.Monic)
    (hsep : (f.map v).Separable) (a : k) (ha : (f.map v).eval a = 0) : ∃ w, f.eval w = 0 ∧ v w = a := by
  obtain ⟨a₀, rfl⟩ := hv a
  have h1 : f.eval a₀ ∈ maximalIdeal W := by
    rw [← hker, RingHom.mem_ker, ← ha, eval_map, eval₂_at_apply]
  have h2 : v (f.derivative.eval a₀) ≠ 0 := by
    have := hsep.eval₂_derivative_ne_zero (RingHom.id k) (x := v a₀) (by simpa using ha)
    rwa [eval₂_id, derivative_map, eval_map, eval₂_at_apply] at this
  obtain ⟨w, hw, hw'⟩ := (IsAdicComplete.henselianRing W (maximalIdeal W)).is_henselian f hf a₀ h1
    ((isUnit_of_ne v hker h2).map _)
  refine ⟨w, hw, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at hw'
  exact hw'
end GlobalTheory.UnitLemma.UnrExt
