-- Prove2me | solution 1 for N25.frickeCuspCharacter
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:07.957368+00:00
-- url     : https://prove2.me/submissions/ab0f2566-9f32-408f-8299-bba3ec3379f7

import Mathlib
import Theorems.Thm_N25_cuspDiamondEigenvalue
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Theorems.Thm_N25_Endgame_pG25_rational
import Theorems.Thm_N25_Endgame_pointDiff_mem_M
import Theorems.Thm_N25_fricke_slash_picard
import Definitions.Def_N25
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace N25

open AlgebraicCurve Endgame

private theorem character_transport
    {A : Type*} [AddCommGroup A] (w s d : A →+ A) (t : A) (n : ℤ)
    (hfix : s t = t) (hd : d t = n • t)
    (hinv : d (w (d t)) = w t)
    (hcov : w (s (d t)) = s (d (w (d t)))) :
    s (w t) = n • w t := by
  rw [hinv, hd, map_zsmul, hfix, map_zsmul] at hcov
  exact hcov.symm

/-- A single Fricke witness gives eigenvalue 57 for the forward diamond on
its cusp image. On the cyclotomic coset 2^k H25 its Galois character is 57^k. -/
theorem _root_.solution
    (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0])
    (hcoeff : pointDiff (pG25 0) (pG25 2)
        ((pG25_degree 0).trans (pG25_degree 2).symm) =
      (6 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm))
    (h71 : (71 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) = 0) :
    let t : J := pointDiff (pG25 0) (pG25 1)
      ((pG25_degree 0).trans (pG25_degree 1).symm)
    ∃ w : FG ≃ₐ[Qbar] FG,
      (∀ (x : FG) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH 25 H25 : Subgroup (GL (Fin 2) ℝ)) k),
        ModularCurve.coeffMap ι (x : LaurentSeries Qbar) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        ModularCurve.coeffMap ι (w x : LaurentSeries Qbar) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ x : J, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      gamma (SemilinearAut.ofAlgAut w • t) =
        (57 : ℤ) • (SemilinearAut.ofAlgAut w • t) ∧
      (∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25) (k : ℕ) (h : H25),
        (∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
        ZMod.unitOfCoprime c hc = (ZMod.unitOfCoprime 2 (by decide)) ^ k * (h : (ZMod 25)ˣ) →
        σ • (SemilinearAut.ofAlgAut w • t) =
          (57 ^ k : ℤ) • (SemilinearAut.ofAlgAut w • t)) := by
  let t : J := pointDiff (pG25 0) (pG25 1)
    ((pG25_degree 0).trans (pG25_degree 1).symm)
  have ht : ∀ σ : Gal, σ • t = t :=
    pointDiff_mem_M (pG25 0) (pG25 1) (pG25_rational 0) (pG25_rational 1)
  have hd := (cuspDiamondEigenvalue hcoeff h71).2
  obtain ⟨w, hspec, hinv, hww, hcov⟩ := fricke_slash_picard ι W hW
  refine ⟨w, hspec, hww, ?_, ?_⟩
  · have hi : gamma (ModularCurve.diamondHBar 25 H25
        (ZMod.unitOfCoprime 2 (by decide)) t) = t := by
      change ModularCurve.diamondHBar 25 H25 _
        (ModularCurve.diamondHBar 25 H25 _ t) = t
      rw [← ModularCurve.diamondHBar_mul]
      have hu : ZMod.unitOfCoprime 13 (by decide) * ZMod.unitOfCoprime 2 (by decide) =
          (1 : (ZMod 25)ˣ) := by decide
      rw [hu]
      exact ModularCurve.diamondHBar_apply_eq_self_of_mem 25 H25 1 H25.one_mem t
    have h := hinv (ZMod.unitOfCoprime 13 (by decide))
      (ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime 2 (by decide)) t)
    change gamma (SemilinearAut.ofAlgAut w • gamma
      (ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime 2 (by decide)) t)) = _ at h
    rw [hi, hd] at h
    rw [show SemilinearAut.ofAlgAut w • ((57 : ℤ) • t) =
      (57 : ℤ) • (SemilinearAut.ofAlgAut w • t) from
        map_zsmul (DistribSMul.toAddMonoidHom J (SemilinearAut.ofAlgAut w)) 57 t] at h
    exact h
  · intro σ c hc k h hχ hcoset
    have hp (n : ℕ) : ModularCurve.diamondHBar 25 H25
        ((ZMod.unitOfCoprime 2 (by decide)) ^ n) t = (57 ^ n : ℤ) • t := by
      induction n with
      | zero =>
          simp only [pow_zero, one_zsmul]
          exact ModularCurve.diamondHBar_apply_eq_self_of_mem 25 H25 1 H25.one_mem t
      | succ n ih =>
          rw [pow_succ, ModularCurve.diamondHBar_mul, hd, map_zsmul, ih, smul_smul]
          rw [mul_comm, ← pow_succ]
    have hdc : ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime c hc) t =
        (57 ^ k : ℤ) • t := by
      rw [hcoset, ModularCurve.diamondHBar_mul,
        ModularCurve.diamondHBar_apply_eq_self_of_mem 25 H25 h h.property t]
      exact hp k
    exact character_transport
      (DistribSMul.toAddMonoidHom J (SemilinearAut.ofAlgAut w))
      (DistribSMul.toAddMonoidHom J σ)
      (ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime c hc))
      t (57 ^ k) (ht σ) hdc
      (hinv (ZMod.unitOfCoprime c hc) t)
      (hcov σ c hc hχ
        (ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime c hc) t))

end N25
