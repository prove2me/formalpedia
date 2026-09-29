-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_relabel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/83dedea9-d7f6-5067-b392-a94a080ee0a7

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

namespace ModularCurve
namespace LevelRelabelling
p2m_export "ModularCurve.LevelRelabelling" "zsmulSection zlinComb RawDrinfeldPair.relabel"
namespace RelabelAction
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

theorem zlinComb_zlinComb_zlinComb (G : RelativeGroupLaw T (projModelStrCR W))
    (hcomm : ∀ x y : Section W, G.mul _ x y = G.mul _ y x)
    (P Q : Section W) (a b c d e f : ℤ) :
    zlinComb G (zlinComb G P Q a b) (zlinComb G P Q c d) e f =
      zlinComb G P Q (a * e + c * f) (b * e + d * f) := by
  letI := G.pointGroup (𝟙 (base (T := T)))
  letI : CommGroup (Section W) := { (G.pointGroup (𝟙 (base (T := T)))) with mul_comm := hcomm }
  have h1 : zlinComb G (zlinComb G P Q a b) (zlinComb G P Q c d) e f =
      (P ^ a * Q ^ b) ^ e * (P ^ c * Q ^ d) ^ f := by
    rw [zlinComb_eq, zlinComb_eq, zlinComb_eq]
  have h2 : zlinComb G P Q (a * e + c * f) (b * e + d * f) =
      P ^ (a * e + c * f) * Q ^ (b * e + d * f) := zlinComb_eq G P Q _ _
  rw [h1, h2, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, zpow_add, zpow_add]
  simp only [mul_assoc, mul_left_comm (Q ^ (b * e)) (P ^ (c * f)) (Q ^ (d * f))]

end ModularCurve.LevelRelabelling.RelabelAction

open _root_.ModularCurve.LevelRelabelling _root_.P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel.ModularCurve.LevelRelabelling in

theorem solution
    {A : Type u} [CommRing A] (𝒢 : GroupLaws A)
    {T : Type u} [CommRing T] [Algebra A T]
    (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hcomm : ∀ P Q : Section x.curve, (𝒢 T x.curve hΔ).mul _ P Q = (𝒢 T x.curve hΔ).mul _ Q P)
    (g g' : Matrix (Fin 2) (Fin 2) ℤ) :
    RawDrinfeldPair.relabel 𝒢 g' (RawDrinfeldPair.relabel 𝒢 g x hΔ) hΔ =
      RawDrinfeldPair.relabel 𝒢 (g * g') x hΔ := by
  show (⟨x.curve, _, _⟩ : RawDrinfeldPair T) = ⟨x.curve, _, _⟩
  simp only [RawDrinfeldPair.relabel, RelabelAction.zlinComb_zlinComb_zlinComb _ hcomm, Matrix.mul_apply,
    Fin.sum_univ_two]

end S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel (solution)
