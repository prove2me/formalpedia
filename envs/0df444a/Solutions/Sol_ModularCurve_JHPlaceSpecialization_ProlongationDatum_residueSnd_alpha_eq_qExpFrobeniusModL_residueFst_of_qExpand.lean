-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0ee97652-a182-5161-95f8-136ed310564e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
import Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel

open scoped MatrixGroups

namespace Res2Frob

theorem coeffMap_residue_cross (A : ValuationSubring (AlgebraicClosure ℚ)) (x y x₁ y₁ : LaurentSeries ↥A)
    (h : coeffMap A.subtype x * coeffMap A.subtype y₁ = coeffMap A.subtype x₁ * coeffMap A.subtype y) :
    coeffMap (IsLocalRing.residue ↥A) x * coeffMap (IsLocalRing.residue ↥A) y₁ =
      coeffMap (IsLocalRing.residue ↥A) x₁ * coeffMap (IsLocalRing.residue ↥A) y := by

  have hinj : Function.Injective (coeffMap A.subtype) := by
    intro a b hab
    apply HahnSeries.ext
    funext k
    apply Subtype.val_injective
    have := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff k) hab
    first | simpa only [coeffMap_coeff] using this | (simp only [coeffMap_coeff] at this; exact this) | exact this
  have h' : x * y₁ = x₁ * y := hinj (by rw [map_mul, map_mul]; exact h)
  rw [← map_mul, ← map_mul, h']

theorem residue₁_mul_coeffMap_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers) (x y : LaurentSeries ↥A)
    (hxF : coeffMap A.subtype x ∈ xHFunctionFieldBar M H) (hyF : coeffMap A.subtype y ∈ xHFunctionFieldBar M H)
    (hxy : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ((Rpd.R₁.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) *
        coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x := by
  obtain ⟨hyR, hyres⟩ := Rpd.residue₁_coeffMap y hyF
  obtain ⟨hxR, hxres⟩ := Rpd.residue₁_coeffMap x hxF

  have hmul : (⟨f, hf⟩ : ↥Rpd.R₁.integers) * ⟨⟨coeffMap A.subtype y, hyF⟩, hyR⟩ =
      ⟨⟨coeffMap A.subtype x, hxF⟩, hxR⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    show ((f * ⟨coeffMap A.subtype y, hyF⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype x
    rw [MulMemClass.coe_mul]
    exact hxy
  have hres := congrArg (fun z : ↥Rpd.R₁.integers =>
    ((Rpd.R₁.residue z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A))) hmul
  simp only [map_mul, MulMemClass.coe_mul] at hres
  rw [hyres, hxres] at hres
  exact hres

theorem coeffMap_qExpand {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem heart_of_hθ
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (x y : LaurentSeries ↥A)
    (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (hxy : ((u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
      coeffMap A.subtype x) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ x' y' : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y' ≠ 0 ∧
      ((θ (α u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y' = coeffMap A.subtype x' ∧
      coeffMap (IsLocalRing.residue ↥A) x' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) =
        qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) x) * coeffMap (IsLocalRing.residue ↥A) y' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨qExpand (↥A) p x, qExpand (↥A) p y, ?_, ?_, ?_⟩
  · rw [coeffMap_qExpand]
    exact fun h => hy (qExpand_injective p (h.trans (map_zero _).symm))
  · rw [hθ (α u) u (hα_coe u), coeffMap_qExpand, coeffMap_qExpand, ← map_mul, hxy]
  · rw [coeffMap_qExpand, coeffMap_qExpand, mul_comm]

theorem qExpand_ne_zero {K : Type} [Field K] (N : ℕ) [NeZero N] {s : LaurentSeries K} (hs : s ≠ 0) : qExpand K N s ≠ 0 :=
  fun h => hs (qExpand_injective N (h.trans (map_zero _).symm))

theorem core
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (θ₀ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ₀ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ₀ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ₀)
    (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers) :
    Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  rw [Rpd.residue₂_eq]

  obtain ⟨x, y, hy, hxy⟩ := (ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ₀ Psp Rpd (α v)).mp h₁
  have hxyv : ((v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
      coeffMap A.subtype x := by rw [← hα_coe]; exact hxy

  obtain ⟨x', y', hy', hxy', hfrob⟩ := heart_of_hθ p M H hpM A α hα_coe θ₀ hθ₀ v x y hy hxyv

  obtain ⟨x₁, y₁, hx₁F, hy₁F, hy₁, hxy₁⟩ :=
    ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (α v) x y hy hxy
  obtain ⟨x₂, y₂, hx₂F, hy₂F, hy₂, hxy₂⟩ :=
    ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (θ₀ (α v)) x' y' hy' hxy'
  have hθ1 : θ₀ (α v) ∈ Rpd.R₁.integers :=
    (ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ₀ Psp Rpd (θ₀ (α v))).mpr
      ⟨x', y', hy', hxy'⟩
  have e₁ := residue₁_mul_coeffMap_eq p M H hpM A θ₀ Psp Rpd (α v) h₁ x₁ y₁ hx₁F hy₁F hxy₁
  have e₂ := residue₁_mul_coeffMap_eq p M H hpM A θ₀ Psp Rpd (θ₀ (α v)) hθ1 x₂ y₂ hx₂F hy₂F hxy₂

  have c₁ : coeffMap (IsLocalRing.residue ↥A) x * coeffMap (IsLocalRing.residue ↥A) y₁ =
      coeffMap (IsLocalRing.residue ↥A) x₁ * coeffMap (IsLocalRing.residue ↥A) y := by
    apply coeffMap_residue_cross
    rw [← hxy, ← hxy₁]; ring
  have c₂ : coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) y₂ =
      coeffMap (IsLocalRing.residue ↥A) x₂ * coeffMap (IsLocalRing.residue ↥A) y' := by
    apply coeffMap_residue_cross
    rw [← hxy', ← hxy₂]; ring

  have f₁ : ((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x := by
    apply mul_right_cancel₀ hy₁
    calc ((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y * coeffMap (IsLocalRing.residue ↥A) y₁
        = (((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y₁) * coeffMap (IsLocalRing.residue ↥A) y := by ring
      _ = coeffMap (IsLocalRing.residue ↥A) x₁ * coeffMap (IsLocalRing.residue ↥A) y := by rw [e₁]
      _ = coeffMap (IsLocalRing.residue ↥A) x * coeffMap (IsLocalRing.residue ↥A) y₁ := c₁.symm
  have f₂ : ((Rpd.R₁.residue ⟨θ₀ (α v), hθ1⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' = coeffMap (IsLocalRing.residue ↥A) x' := by
    apply mul_right_cancel₀ hy₂
    calc ((Rpd.R₁.residue ⟨θ₀ (α v), hθ1⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y' * coeffMap (IsLocalRing.residue ↥A) y₂
        = (((Rpd.R₁.residue ⟨θ₀ (α v), hθ1⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y₂) * coeffMap (IsLocalRing.residue ↥A) y' := by ring
      _ = coeffMap (IsLocalRing.residue ↥A) x₂ * coeffMap (IsLocalRing.residue ↥A) y' := by rw [e₂]
      _ = coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) y₂ := c₂.symm

  have key : ((Rpd.R₁.residue ⟨θ₀ (α v), hθ1⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = qExpand (ResidueField ↥A) p ((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) := by
    have hne : coeffMap (IsLocalRing.residue ↥A) y' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) ≠ 0 := mul_ne_zero hy' (qExpand_ne_zero p hy)
    apply mul_right_cancel₀ hne
    calc ((Rpd.R₁.residue ⟨θ₀ (α v), hθ1⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * (coeffMap (IsLocalRing.residue ↥A) y' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y))
        = (((Rpd.R₁.residue ⟨θ₀ (α v), hθ1⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y') * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) := by ring
      _ = coeffMap (IsLocalRing.residue ↥A) x' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) := by rw [f₂]
      _ = qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) x) * coeffMap (IsLocalRing.residue ↥A) y' := hfrob
      _ = qExpand (ResidueField ↥A) p (((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y) * coeffMap (IsLocalRing.residue ↥A) y' := by rw [f₁]
      _ = qExpand (ResidueField ↥A) p ((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * (coeffMap (IsLocalRing.residue ↥A) y' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y)) := by rw [map_mul]; ring

  apply Subtype.ext
  rw [coe_qExpFrobeniusModL]
  exact key

end Res2Frob

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (θ₀ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ₀ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ₀ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ₀) :
    ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩) := by
  intro v h₁ h₂
  exact Res2Frob.core p M H hpM hpM2 hHp A hA α hα_coe θ₀ hθ₀ Psp Rpd v h₁ h₂

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand (solution)
