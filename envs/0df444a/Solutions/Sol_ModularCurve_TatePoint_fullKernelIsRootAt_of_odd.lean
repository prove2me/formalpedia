-- Prove2me | solution 1 for ModularCurve.TatePoint.fullKernelIsRootAt_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e394d22c-2b9d-59c4-9997-70325fbc01f0

import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_ModularCurve_CycSubRootBridgeOdd
import Definitions.Def_ModularCurve_CycSubRootBridgeN
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd.ModularCurve WeierstrassCurve P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd.WeierstrassCurve Polynomial"
open scoped Classical

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map toAffine Δ j fullKernelQuotient fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet oddOrderSummingSet veluQuotient veluQuotient_oddOrderSummingSet_discriminant_ne_zero zmultiples_eq_of_veluQuotient_j_eq_of_transcendental"
p2m_open "WeierstrassCurve"

theorem j_congr {R : Type*} [CommRing R] {X Y : WeierstrassCurve R} (h : X = Y) (hX : X.IsElliptic)
    (hY : Y.IsElliptic) : @WeierstrassCurve.j R _ X hX = @WeierstrassCurve.j R _ Y hY := by
  subst h
  rfl

private theorem _root_.WeierstrassCurve.fullKernelQuotient_eq_veluQuotient_of_odd_aux {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) {N : ℕ} (hN : Odd N) (hQ : addOrderOf Q = N) :
    W.fullKernelQuotient Q N = W.veluQuotient (W.oddOrderSummingSet Q ((N - 1) / 2)) := by
  obtain ⟨m, rfl⟩ := hN
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm]
  exact W.fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet Q m hQ

p2m_export "WeierstrassCurve" "fullKernelQuotient_eq_veluQuotient_of_odd_aux"

private theorem _root_.WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero_of_odd {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) [W.IsElliptic] (N : ℕ) [NeZero N] (hN : Odd N)
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  obtain ⟨m, rfl⟩ := hN
  rw [W.fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet Q m hQ]
  exact WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero h2 W m Q hQ

p2m_export "WeierstrassCurve" "fullKernelQuotient_discriminant_ne_zero_of_odd"

private theorem _root_.WeierstrassCurve.zmultiples_eq_of_fullKernelQuotient_j_eq_of_transcendental_of_odd
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (ht : Transcendental ℚ W.j) (N : ℕ) [NeZero N] (hN : Odd N) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (hΔ' : (W.fullKernelQuotient Q' N).Δ ≠ 0)
    (hj : haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.fullKernelQuotient Q' N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.fullKernelQuotient Q N).j = (W.fullKernelQuotient Q' N).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' := by
  obtain ⟨m, rfl⟩ := hN
  have hWQ := W.fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet Q m hQ
  have hWQ' := W.fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet Q' m hQ'
  have hΔ₁ : (W.veluQuotient (W.oddOrderSummingSet Q m)).Δ ≠ 0 := by rw [← hWQ]; exact hΔ
  have hΔ₂ : (W.veluQuotient (W.oddOrderSummingSet Q' m)).Δ ≠ 0 := by rw [← hWQ']; exact hΔ'
  rw [j_congr hWQ ⟨isUnit_iff_ne_zero.mpr hΔ⟩ ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩,
    j_congr hWQ' ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ ⟨isUnit_iff_ne_zero.mpr hΔ₂⟩] at hj
  exact WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental W ht m Q Q' hQ hQ' hΔ₁ hΔ₂ hj

p2m_export "WeierstrassCurve" "zmultiples_eq_of_fullKernelQuotient_j_eq_of_transcendental_of_odd"
end WeierstrassCurve

namespace ModularCurve p2m_export "ModularCurve" "TatePoint.dictOdd TatePoint.Qbar TatePoint.nearCurve TatePoint.CycSubH TatePoint.RootsAt ModularPolynomialData ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq TatePoint.dictN" namespace ModularPolynomialData p2m_export "ModularCurve.ModularPolynomialData" "Φ isRoot_map_j_veluQuotient_j_of_addOrderOf_eq" end ModularCurve.ModularPolynomialData
p2m_open_scoped "ModularCurve ModularCurve.ModularPolynomialData" in

theorem ModularCurve.ModularPolynomialData.isRoot_map_j_fullKernelQuotient_j_of_odd
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (N : ℕ) [NeZero N] (hN : Odd N) (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData N) :
    haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom
      (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot
      (W.fullKernelQuotient Q N).j := by
  obtain ⟨m, rfl⟩ := hN
  have hWQ := W.fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet Q m hQ
  have hΔ₁ : (W.veluQuotient (W.oddOrderSummingSet Q m)).Δ ≠ 0 := by rw [← hWQ]; exact hΔ
  rw [WeierstrassCurve.j_congr hWQ ⟨isUnit_iff_ne_zero.mpr hΔ⟩ ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩]
  exact ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq W m Q hQ hΔ₁ data

namespace ModularCurve
p2m_export "ModularCurve" "TatePoint.dictOdd TatePoint.Qbar TatePoint.nearCurve TatePoint.CycSubH TatePoint.RootsAt ModularPolynomialData ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq TatePoint.dictN"
namespace TatePoint
p2m_export "ModularCurve.TatePoint" "cycSubRootOdd rootsEquivCycSubHOdd rootsEquivCycSubHOdd_apply_eq_iff dictOdd cycSubGen addOrderOf_cycSubGen Qbar H nearCurve CycSubH RootsAt nearCurve_j_transcendental FullKernelIsRootAt FullKernelInjAt FullKernelDiscAt cycSubRootN rootsEquivCycSubHN rootsEquivCycSubHN_apply_eq_iff dictN"
p2m_open "ModularCurve.TatePoint ModularCurve"

private theorem cycSubRootN_eq_cycSubRootOdd_aux (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N] (hN : Odd N)
    (hW1 : FullKernelIsRootAt N) (hW3 : FullKernelDiscAt N) (data : ModularPolynomialData N)
    (G : CycSubH E N) : cycSubRootN E hW1 hW3 data G = cycSubRootOdd E hN data G :=
  Subtype.ext (WeierstrassCurve.j_congr
    (E.fullKernelQuotient_eq_veluQuotient_of_odd_aux (cycSubGen E G) hN (addOrderOf_cycSubGen E G)) _ _)

private theorem rootsEquivCycSubHN_eq_rootsEquivCycSubHOdd_aux (E : WeierstrassCurve H) [E.IsElliptic] {N : ℕ} [NeZero N]
    (hN : Odd N) (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (data : ModularPolynomialData N) (hj : Transcendental Qbar E.j) :
    rootsEquivCycSubHN E hW1 hW2 hW3 data hj = rootsEquivCycSubHOdd E hN data hj := by
  ext r : 1
  rw [rootsEquivCycSubHN_apply_eq_iff, cycSubRootN_eq_cycSubRootOdd_aux E hN,
    ← rootsEquivCycSubHOdd_apply_eq_iff E hN data hj r (rootsEquivCycSubHOdd E hN data hj r)]

private theorem dictN_eq_dictOdd_aux (N : ℕ) [NeZero N] (hN : Odd N) (data : ModularPolynomialData N) (j₀ : Qbar)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N) :
    dictN N data j₀ hW1 hW2 hW3 = dictOdd N hN data j₀ :=
  rootsEquivCycSubHN_eq_rootsEquivCycSubHOdd_aux (nearCurve j₀) hN hW1 hW2 hW3 data
    (nearCurve_j_transcendental j₀)

private theorem fullKernelIsRootAt_of_odd_aux (N : ℕ) [NeZero N] (hN : Odd N) : FullKernelIsRootAt N :=
  fun W _ Q hQ hΔ data =>
    ModularCurve.ModularPolynomialData.isRoot_map_j_fullKernelQuotient_j_of_odd W N hN Q hQ hΔ data

private theorem fullKernelInjAt_of_odd_aux (N : ℕ) [NeZero N] (hN : Odd N) : FullKernelInjAt N :=
  fun W _ ht Q Q' hQ hQ' hΔ hΔ' hj =>
    W.zmultiples_eq_of_fullKernelQuotient_j_eq_of_transcendental_of_odd ht N hN Q Q' hQ hQ' hΔ hΔ' hj

private theorem fullKernelDiscAt_of_odd_aux (N : ℕ) [NeZero N] (hN : Odd N) : FullKernelDiscAt N :=
  fun h2 W _ Q hQ => W.fullKernelQuotient_discriminant_ne_zero_of_odd h2 N hN Q hQ

def dictNOdd (N : ℕ) [NeZero N] (hN : Odd N) (data : ModularPolynomialData N) (j₀ : Qbar) :
    RootsAt data (nearCurve j₀).j ≃ CycSubH (nearCurve j₀) N :=
  dictN N data j₀ (fullKernelIsRootAt_of_odd_aux N hN) (fullKernelInjAt_of_odd_aux N hN)
    (fullKernelDiscAt_of_odd_aux N hN)

theorem dictNOdd_eq_dictOdd (N : ℕ) [NeZero N] (hN : Odd N) (data : ModularPolynomialData N) (j₀ : Qbar) :
    dictNOdd N hN data j₀ = dictOdd N hN data j₀ :=
  dictN_eq_dictOdd_aux N hN data j₀ _ _ _

end ModularCurve.TatePoint

end

noncomputable example (data : ModularCurve.ModularPolynomialData 3) (j₀ : ModularCurve.TatePoint.Qbar) :
    ModularCurve.TatePoint.RootsAt data (ModularCurve.TatePoint.nearCurve j₀).j ≃
      ModularCurve.TatePoint.CycSubH (ModularCurve.TatePoint.nearCurve j₀) 3 :=
  ModularCurve.TatePoint.dictNOdd 3 (by decide) data j₀

open scoped Classical
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd.ModularCurve _root_.ModularCurve.TatePoint _root_.P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd.ModularCurve.TatePoint in

theorem solution (N : ℕ) [NeZero N] (hN : Odd N) : FullKernelIsRootAt N :=
  ModularCurve.TatePoint.fullKernelIsRootAt_of_odd_aux N hN

#print axioms solution

end S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd
end P2MW
export P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd (solution)
