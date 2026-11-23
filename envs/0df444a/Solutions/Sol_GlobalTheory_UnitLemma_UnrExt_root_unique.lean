-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrExt.root_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:39.243137+00:00
-- url     : https://prove2.me/submissions/a4e1d5f9-ba82-48ef-be27-2060df3b5efe

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
theorem _root_.solution (f : W[X]) (hsep : (f.map v).Separable) {a b : W} (ha : f.eval a = 0) (hb : f.eval b = 0)
    (hab : v a = v b) : a = b := by
  have ha' : (f.map v).eval (v a) = 0 := by rw [eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : v (f.derivative.eval a) ≠ 0 := by
    have := hsep.eval₂_derivative_ne_zero (RingHom.id k) (x := v a) (by simpa using ha')
    rwa [eval₂_id, derivative_map, eval_map, eval₂_at_apply] at this
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f) ha hb ?_ (isUnit_of_ne v hker h2)
  have : a - b ∈ maximalIdeal W := by rw [← hker, RingHom.mem_ker, map_sub, hab, sub_self]
  exact this
end GlobalTheory.UnitLemma.UnrExt
