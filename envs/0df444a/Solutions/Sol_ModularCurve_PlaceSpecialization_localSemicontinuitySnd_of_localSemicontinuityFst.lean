-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.localSemicontinuitySnd_of_localSemicontinuityFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1d088645-0b89-5378-bf37-f55a1b2131bb

import Definitions.Def_ModularCurve_ChartSemicontinuity
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_atkinLehnerBar_smul_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_localSemicontinuitySnd_of_localSemicontinuityFst
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_localSemicontinuitySnd_of_localSemicontinuityFst.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_localSemicontinuitySnd_of_localSemicontinuityFst.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence atkinLehnerInvolutionFull geomAut atkinLehnerInvolutionFull_apply_apply"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst reduceSnd IsStrictFst IsStrictSnd fstDiv sndDiv reduceFst_atkinLehnerBar_smul isStrictFst_atkinLehnerBar_smul_iff"
namespace SndTransport
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

theorem snd_filter_mapDomain {α β M : Type*} [AddCommMonoid M] (e : α → β) (p : β → Prop)
    [DecidablePred p] [DecidablePred (fun a => p (e a))] (D : α →₀ M) :
    (Finsupp.mapDomain e D).filter p = Finsupp.mapDomain e (D.filter (fun a => p (e a))) := by
  classical
  induction D using Finsupp.induction with
  | zero => simp only [Finsupp.filter_zero, Finsupp.mapDomain_zero]
  | single_add a m D _ _ ih =>
      rw [Finsupp.mapDomain_add, Finsupp.filter_add, Finsupp.filter_add, Finsupp.mapDomain_add, ih,
        Finsupp.mapDomain_single]
      congr 1
      by_cases h : p (e a)
      · rw [Finsupp.filter_single_of_pos _ h,
          Finsupp.filter_single_of_pos (fun a => p (e a)) (show p (e a) from h),
          Finsupp.mapDomain_single]
      · rw [Finsupp.filter_single_of_neg _ h,
          Finsupp.filter_single_of_neg (fun a => p (e a)) (show ¬ p (e a) from h),
          Finsupp.mapDomain_zero]

theorem snd_filter_congr {α M : Type*} [Zero M] (p p' : α → Prop) [DecidablePred p]
    [DecidablePred p'] (h : ∀ a, p a ↔ p' a) (D : α →₀ M) : D.filter p = D.filter p' := by
  ext a
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases ha : p a
  · rw [if_pos ha, if_pos ((h a).mp ha)]
  · rw [if_neg ha, if_neg (fun h' => ha ((h a).mpr h'))]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem snd_atkinLehnerInvolutionFull_mul_self (hqN : ¬ q ∣ N) :
    atkinLehnerInvolutionFull N q * atkinLehnerInvolutionFull N q = 1 :=
  AlgEquiv.ext fun x => atkinLehnerInvolutionFull_apply_apply N q hqN x

theorem snd_atkinLehnerBar_mul_self (hqN : ¬ q ∣ N) :
    ProlongationTuple.atkinLehnerBar N q * ProlongationTuple.atkinLehnerBar N q = 1 := by
  unfold ProlongationTuple.atkinLehnerBar
  rw [← map_mul, snd_atkinLehnerInvolutionFull_mul_self hqN, map_one]

theorem snd_atkinLehnerBar_apply_apply (hqN : ¬ q ∣ N) (f : modularFunctionFieldBar (N * q)) :
    ProlongationTuple.atkinLehnerBar N q (ProlongationTuple.atkinLehnerBar N q f) = f := by
  rw [← AlgEquiv.mul_apply, snd_atkinLehnerBar_mul_self hqN, AlgEquiv.one_apply]

theorem snd_atkinLehnerBar_inv (hqN : ¬ q ∣ N) :
    (ProlongationTuple.atkinLehnerBar N q)⁻¹ = ProlongationTuple.atkinLehnerBar N q :=
  inv_eq_of_mul_eq_one_right (snd_atkinLehnerBar_mul_self hqN)

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem snd_residueFst_congr {x y : modularFunctionFieldBar (N * q)} (hx : x ∈ R.R₁.integers)
    (hy : y ∈ R.R₁.integers) (h : x = y) : R.R₁.residue ⟨x, hx⟩ = R.R₁.residue ⟨y, hy⟩ := by
  subst h; rfl

theorem snd_mapDomain_reduceFst_fstDiv_smul (hqN : ¬ q ∣ N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv (ProlongationTuple.atkinLehnerBar N q • D)) =
      Finsupp.mapDomain P.reduceSnd (P.sndDiv D) := by
  classical
  have hF : (P.reduceFst ∘ fun W => ProlongationTuple.atkinLehnerBar N q • W) = P.reduceSnd :=
    funext fun W => reduceFst_atkinLehnerBar_smul P hqN W
  unfold PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv
  rw [Divisor.smul_def, snd_filter_mapDomain, ← Finsupp.mapDomain_comp, hF,
    snd_filter_congr (fun W => P.IsStrictFst (ProlongationTuple.atkinLehnerBar N q • W)) P.IsStrictSnd
      (fun W => isStrictFst_atkinLehnerBar_smul_iff P hqN W)]

end ModularCurve.PlaceSpecialization.SndTransport

open ModularCurve.PlaceSpecialization.SndTransport

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hfst : ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k N),
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
          (∀ W, P.IsStrictFst W → P.reduceFst W = v → 0 ≤ D W) →
          Finsupp.mapDomain P.reduceFst (P.fstDiv D) v ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ u : Place k (modularFunctionFieldC k N),
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr u) ≠ u →
          (∀ W, P.IsStrictSnd W → P.reduceSnd W = u → 0 ≤ D W) →
          Finsupp.mapDomain P.reduceSnd (P.sndDiv D) u ≤ u.ord (R.residue₂ ⟨f, h₂⟩) := by
  classical
  intro f h₁ h₂ hne₁ hne₂ D hD u hu hpole
  set w := ProlongationTuple.atkinLehnerBar N q with hw_def

  have hg₁ : w f ∈ R.R₁.integers := (R.mem_integers₂_iff f).mp h₂
  have hg₂ : w f ∈ R.R₂.integers :=
    (R.mem_integers₂_iff (w f)).mpr (by rw [snd_atkinLehnerBar_apply_apply hqN]; exact h₁)
  have hres₁ : R.R₁.residue ⟨w f, hg₁⟩ = R.R₂.residue ⟨f, h₂⟩ := (R.residue₂_eq f h₂).symm
  have hres₂ : R.R₂.residue ⟨w f, hg₂⟩ = R.R₁.residue ⟨f, h₁⟩ :=
    (R.residue₂_eq (w f) hg₂).trans
      (snd_residueFst_congr R _ h₁ (snd_atkinLehnerBar_apply_apply hqN f))
  have hgne₁ : R.R₁.residue ⟨w f, hg₁⟩ ≠ 0 := by rw [hres₁]; exact hne₂
  have hgne₂ : R.R₂.residue ⟨w f, hg₂⟩ ≠ 0 := by rw [hres₂]; exact hne₁

  have hD' : ∀ W, (w • D) W = W.ord (w f) := by
    intro W
    rw [Divisor.smul_apply, hD (w⁻¹ • W)]
    have h := Place.ord_smul w (w⁻¹ • W) f
    rw [smul_inv_smul] at h
    exact h.symm

  have hpole' : ∀ W, P.IsStrictFst W → P.reduceFst W = u → 0 ≤ (w • D) W := by
    intro W hW hWu
    have hWV : w • (w⁻¹ • W) = W := smul_inv_smul w W
    rw [← hWV] at hW hWu ⊢
    rw [Divisor.smul_apply_smul]
    refine hpole _ ((isStrictFst_atkinLehnerBar_smul_iff P hqN _).mp hW) ?_
    rw [← reduceFst_atkinLehnerBar_smul P hqN]
    exact hWu

  have key := hfst (w f) hg₁ hg₂ hgne₁ hgne₂ (w • D) hD' u hu hpole'
  rw [snd_mapDomain_reduceFst_fstDiv_smul hqN] at key
  have hρ : R.residue₁ ⟨w f, hg₁⟩ = R.residue₂ ⟨f, h₂⟩ := by
    rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₂_apply, hres₁]
  rw [hρ] at key
  exact key

end S_ModularCurve_PlaceSpecialization_localSemicontinuitySnd_of_localSemicontinuityFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_localSemicontinuitySnd_of_localSemicontinuityFst (solution)
