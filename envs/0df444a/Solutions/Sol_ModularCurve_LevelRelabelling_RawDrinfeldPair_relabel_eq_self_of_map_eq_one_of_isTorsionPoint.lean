-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_self_of_map_eq_one_of_isTorsionPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8095f421-ebbc-50f4-a3fd-1513f0da8118

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

namespace ModularCurve
namespace LevelRelabelling
p2m_export "ModularCurve.LevelRelabelling" "zsmulSection zlinComb RawDrinfeldPair.relabel"
namespace RelabelTrivial
p2m_open "ModularCurve.LevelRelabelling ModularCurve"

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T}

theorem nsmul_eq_pow (G : RelativeGroupLaw T (projModelStrCR W)) (k : ℕ) (P : Section W) :
    letI := G.pointGroup (𝟙 (base (T := T)))
    G.nsmul _ k P = P ^ k := by
  letI := G.pointGroup (𝟙 (base (T := T)))
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]
      rfl

theorem zsmulSection_eq_zpow (G : RelativeGroupLaw T (projModelStrCR W)) (n : ℤ) (P : Section W) :
    letI := G.pointGroup (𝟙 (base (T := T)))
    zsmulSection G n P = P ^ n := by
  letI := G.pointGroup (𝟙 (base (T := T)))
  cases n with
  | ofNat k =>
      show G.nsmul _ k P = P ^ (Int.ofNat k)
      rw [nsmul_eq_pow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc k =>
      show G.inv _ (G.nsmul _ (k + 1) P) = P ^ (Int.negSucc k)
      rw [nsmul_eq_pow, zpow_negSucc]
      rfl

theorem zlinComb_eq (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) (a b : ℤ) :
    letI := G.pointGroup (𝟙 (base (T := T)))
    zlinComb G P Q a b = P ^ a * Q ^ b := by
  letI := G.pointGroup (𝟙 (base (T := T)))
  show G.mul _ (zsmulSection G a P) (zsmulSection G b Q) = P ^ a * Q ^ b
  rw [zsmulSection_eq_zpow, zsmulSection_eq_zpow]
  rfl

theorem zpow_eq_zpow_of_intCast_eq (G : RelativeGroupLaw T (projModelStrCR W)) (n : ℕ) (P : Section W)
    (hP : G.IsTorsionPoint (𝟙 _) n P) (a r : ℤ) (h : ((a : ℤ) : ZMod n) = (r : ZMod n)) :
    letI := G.pointGroup (𝟙 (base (T := T)))
    P ^ a = P ^ r := by
  letI := G.pointGroup (𝟙 (base (T := T)))
  have hn : P ^ (n : ℤ) = 1 := by
    rw [zpow_natCast, ← nsmul_eq_pow]
    exact hP
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub r a n).1 h.symm
  have ha : a = r + n * k := by omega
  rw [ha, zpow_add, zpow_mul, hn, one_zpow, mul_one]

theorem zlinComb_eq_left (G : RelativeGroupLaw T (projModelStrCR W)) (n : ℕ) (P Q : Section W)
    (hP : G.IsTorsionPoint (𝟙 _) n P) (hQ : G.IsTorsionPoint (𝟙 _) n Q)
    (a b : ℤ) (ha : ((a : ℤ) : ZMod n) = 1) (hb : ((b : ℤ) : ZMod n) = 0) :
    zlinComb G P Q a b = P := by
  letI := G.pointGroup (𝟙 (base (T := T)))
  have h1 := zpow_eq_zpow_of_intCast_eq G n P hP a 1 (by rw [ha, Int.cast_one])
  have h2 := zpow_eq_zpow_of_intCast_eq G n Q hQ b 0 (by rw [hb, Int.cast_zero])
  have h3 : zlinComb G P Q a b = P ^ a * Q ^ b := zlinComb_eq G P Q a b
  rw [h3, h1, h2, zpow_one, zpow_zero, mul_one]

theorem zlinComb_eq_right (G : RelativeGroupLaw T (projModelStrCR W)) (n : ℕ) (P Q : Section W)
    (hP : G.IsTorsionPoint (𝟙 _) n P) (hQ : G.IsTorsionPoint (𝟙 _) n Q)
    (a b : ℤ) (ha : ((a : ℤ) : ZMod n) = 0) (hb : ((b : ℤ) : ZMod n) = 1) :
    zlinComb G P Q a b = Q := by
  letI := G.pointGroup (𝟙 (base (T := T)))
  have h1 := zpow_eq_zpow_of_intCast_eq G n P hP a 0 (by rw [ha, Int.cast_zero])
  have h2 := zpow_eq_zpow_of_intCast_eq G n Q hQ b 1 (by rw [hb, Int.cast_one])
  have h3 : zlinComb G P Q a b = P ^ a * Q ^ b := zlinComb_eq G P Q a b
  rw [h3, h1, h2, zpow_one, zpow_zero, one_mul]

end ModularCurve.LevelRelabelling.RelabelTrivial

open _root_.ModularCurve.LevelRelabelling _root_.P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint.ModularCurve.LevelRelabelling in

theorem solution
    {A : Type u} [CommRing A] (𝒢 : GroupLaws A)
    {T : Type u} [CommRing T] [Algebra A T]
    (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ) (n : ℕ)
    (hP : (𝒢 T x.curve hΔ).IsTorsionPoint (𝟙 _) n x.P) (hQ : (𝒢 T x.curve hΔ).IsTorsionPoint (𝟙 _) n x.Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.map (Int.castRingHom (ZMod n)) = 1) :
    RawDrinfeldPair.relabel 𝒢 g x hΔ = x := by
  have h00 : ((g 0 0 : ℤ) : ZMod n) = 1 := by
    have := congrFun (congrFun hg 0) 0; simpa using this
  have h10 : ((g 1 0 : ℤ) : ZMod n) = 0 := by
    have := congrFun (congrFun hg 1) 0; simpa using this
  have h01 : ((g 0 1 : ℤ) : ZMod n) = 0 := by
    have := congrFun (congrFun hg 0) 1; simpa using this
  have h11 : ((g 1 1 : ℤ) : ZMod n) = 1 := by
    have := congrFun (congrFun hg 1) 1; simpa using this
  obtain ⟨c, P, Q⟩ := x
  show (⟨c, _, _⟩ : RawDrinfeldPair T) = ⟨c, P, Q⟩
  rw [RelabelTrivial.zlinComb_eq_left _ n P Q hP hQ _ _ h00 h10,
    RelabelTrivial.zlinComb_eq_right _ n P Q hP hQ _ _ h01 h11]

end S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint (solution)
