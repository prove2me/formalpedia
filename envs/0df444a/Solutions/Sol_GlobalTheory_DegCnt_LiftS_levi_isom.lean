-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.levi_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:47:16.591596+00:00
-- url     : https://prove2.me/submissions/d9e953dc-1a8c-476f-b5a9-f3dda2bc6377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_levi_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (H : HermSpace K V) (p q : V →ₗ[K] V) (s : V ≃ₗ[K] V)
    (adj : ∀ x y, H.B (p x) y = H.B x (q y)) (pp : ∀ x, p (p x) = p x) (qq : ∀ x, q (q x) = q x)
    (pq : ∀ x, p (q x) = 0) (qp : ∀ x, q (p x) = 0) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)
    (h1 : ∀ x, p (s (p x)) = s (p x)) (h2 : ∀ x, p (s.symm (p x)) = s.symm (p x)) (x y : V) :
    H.B (levi p q s x) (levi p q s y) = H.B x y := by
  have hqa : ∀ v w, H.B (q v) w = H.B v (p w) := by
    intro v w
    rw [← H.herm w (q v), ← adj w v, H.herm]
  have hpp0 : ∀ v w, H.B (p v) (p w) = 0 := by
    intro v w
    rw [adj, qp, map_zero]
  have hqq0 : ∀ v w, H.B (q v) (q w) = 0 := by
    intro v w
    rw [hqa, pq, map_zero]
  have hsq : ∀ w, q w = 0 → q (s w) = 0 := by
    intro w hw
    apply H.nondeg
    intro t
    rw [hqa]
    have e : p t = s (p (s.symm (p t))) := by rw [h2 t, LinearEquiv.apply_symm_apply]
    rw [e, hs, ← hqa, hw, map_zero, LinearMap.zero_apply]
  have hpv : ∀ v w, p v = v → H.B v (q w) = H.B v w := by
    intro v w hv
    have e : H.B v (w - q w) = 0 := by
      rw [← hv, adj, map_sub, qq, sub_self, map_zero]
    rw [map_sub, sub_eq_zero] at e
    exact e.symm
  have hpv' : ∀ v w, p v = v → H.B (q w) v = H.B w v := by
    intro v w hv
    have e : H.B (w - q w) v = 0 := by
      rw [← hv, ← hqa, map_sub, qq, sub_self, map_zero, LinearMap.zero_apply]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e
    exact e.symm
  obtain ⟨u, hu⟩ : ∃ u, x - p x - q x = u := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', y - p y - q y = u' := ⟨_, rfl⟩
  have pu : p u = 0 := by rw [← hu]; simp [pp, pq]
  have qu : q u = 0 := by rw [← hu]; simp [qp, qq]
  have pu' : p u' = 0 := by rw [← hu']; simp [pp, pq]
  have qu' : q u' = 0 := by rw [← hu']; simp [qp, qq]
  have hx : x = p x + u + q x := by rw [← hu]; abel
  have hy : y = p y + u' + q y := by rw [← hu']; abel
  have hxy : H.B x y = H.B (p x) (q y) + H.B u u' + H.B (q x) (p y) := by
    have f1 := hpp0 x y
    have f2 : H.B (p x) u' = 0 := by rw [adj, qu', map_zero]
    have f3 : H.B u (p y) = 0 := by rw [← hqa, qu, map_zero, LinearMap.zero_apply]
    have f4 : H.B u (q y) = 0 := by rw [← adj, pu, map_zero, LinearMap.zero_apply]
    have f5 : H.B (q x) u' = 0 := by rw [hqa, pu', map_zero]
    have f6 := hqq0 x y
    have hexp : H.B (p x + u + q x) (p y + u' + q y) = H.B (p x) (p y) + H.B (p x) u' + H.B (p x) (q y) +
        H.B u (p y) + H.B u u' + H.B u (q y) + H.B (q x) (p y) + H.B (q x) u' + H.B (q x) (q y) := by
      simp only [map_add, LinearMap.add_apply]
      ring
    calc H.B x y = H.B (p x + u + q x) (p y + u' + q y) := by rw [← hx, ← hy]
      _ = _ := by rw [hexp, f1, f2, f3, f4, f5, f6]; ring
  rw [levi_apply, levi_apply]
  simp only [LinearEquiv.coe_coe]
  rw [hu, hu', hsq u qu, hsq u' qu', sub_zero, sub_zero]
  have e1 : H.B (s (p x)) (s (p y)) = 0 := by rw [hs]; exact hpp0 x y
  have e2 : H.B (s (p x)) (s u') = 0 := by rw [hs, adj, qu', map_zero]
  have e3 : H.B (s (p x)) (p (s u')) = 0 := by rw [← h1 x]; exact hpp0 _ _
  have e4 : H.B (s (p x)) (q (s (q y))) = H.B (p x) (q y) := by rw [hpv _ _ (h1 x), hs]
  have e5 : H.B (s u) (s (p y)) = 0 := by rw [hs, ← hqa, qu, map_zero, LinearMap.zero_apply]
  have e6 : H.B (s u) (s u') = H.B u u' := hs u u'
  have e7 : H.B (s u) (p (s u')) = 0 := by rw [← hqa, hsq u qu, map_zero, LinearMap.zero_apply]
  have e8 : H.B (s u) (q (s (q y))) = H.B (p (s u)) (s (q y)) := (adj (s u) (s (q y))).symm
  have e9 : H.B (p (s u)) (s (p y)) = 0 := by rw [← h1 y]; exact hpp0 _ _
  have e10 : H.B (p (s u)) (s u') = 0 := by rw [adj, hsq u' qu', map_zero]
  have e11 : H.B (p (s u)) (p (s u')) = 0 := hpp0 _ _
  have e12 : H.B (p (s u)) (q (s (q y))) = H.B (p (s u)) (s (q y)) := by
    rw [adj (s u) (q (s (q y))), qq, ← adj (s u) (s (q y))]
  have e13 : H.B (q (s (q x))) (s (p y)) = H.B (q x) (p y) := by rw [hpv' _ _ (h1 y), hs]
  have e14 : H.B (q (s (q x))) (s u') = H.B (s (q x)) (p (s u')) := hqa _ _
  have e15 : H.B (q (s (q x))) (p (s u')) = H.B (s (q x)) (p (s u')) := by rw [hqa, pp]
  have e16 : H.B (q (s (q x))) (q (s (q y))) = 0 := hqq0 _ _
  have hexp : H.B (s (p x) + (s u - p (s u)) + q (s (q x))) (s (p y) + (s u' - p (s u')) + q (s (q y))) =
      H.B (s (p x)) (s (p y)) + H.B (s (p x)) (s u') - H.B (s (p x)) (p (s u')) + H.B (s (p x)) (q (s (q y))) +
      H.B (s u) (s (p y)) + H.B (s u) (s u') - H.B (s u) (p (s u')) + H.B (s u) (q (s (q y))) -
      H.B (p (s u)) (s (p y)) - H.B (p (s u)) (s u') + H.B (p (s u)) (p (s u')) - H.B (p (s u)) (q (s (q y))) +
      H.B (q (s (q x))) (s (p y)) + H.B (q (s (q x))) (s u') - H.B (q (s (q x))) (p (s u')) +
      H.B (q (s (q x))) (q (s (q y))) := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    ring
  linear_combination hexp + e1 + e2 - e3 + e4 + e5 + e6 - e7 + e8 - e9 - e10 + e11 - e12 + e13 + e14 - e15 + e16 - hxy
end GlobalTheory.DegCnt.LiftS
