-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.isModel_of_divisorLawFst_of_cuspLawInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d5f7e6d8-ae01-5c35-af87-d5f36f3fc75f

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty.ModularCurve.PlaceSpecialization.ProlongationTuple"

noncomputable section

private theorem atkinLehner_atkinLehnerInvolutionFull_mul_self {N q : ℕ} [Fact q.Prime] :
    atkinLehnerInvolutionFull N q * atkinLehnerInvolutionFull N q = 1 := by
  have hq : q.Prime := Fact.out
  by_cases h : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q),
      IsAtkinLehnerAutFull N q σ
  · have hAL := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q h
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨x, hx⟩ := x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        obtain ⟨d, hne, hdvd, rfl⟩ := hy
        haveI := hne
        by_cases hqd : q ∣ d
        · obtain ⟨d', rfl⟩ : ∃ d', d = d' * q := ⟨d / q, (Nat.div_mul_cancel hqd).symm⟩
          haveI : NeZero d' := ⟨fun h0 => (NeZero.ne (d' * q)) (by rw [h0, zero_mul])⟩
          have hd'N : d' ∣ N := Nat.dvd_of_mul_dvd_mul_right hq.pos hdvd
          have h1 := (hAL d' inferInstance hd'N).1
          have h2 := (hAL d' inferInstance hd'N).2
          rw [h2, h1]
        · have hdN : d ∣ N :=
            Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd).symm hdvd
          have h1 := (hAL d inferInstance hdN).1
          have h2 := (hAL d inferInstance hdN).2
          rw [h1, h2]
    | algebraMap c =>
        have hc : (⟨algebraMap ℚ (LaurentSeries ℚ) c, IntermediateField.algebraMap_mem _ c⟩ :
              modularFunctionFieldFull (N * q))
            = ((c : ℚ) : modularFunctionFieldFull (N * q)) :=
          Subtype.ext (eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) c)
        rw [hc, map_ratCast, map_ratCast]
    | add y z hy hz ihy ihz =>
        show atkinLehnerInvolutionFull N q (atkinLehnerInvolutionFull N q
          ((⟨y, hy⟩ : modularFunctionFieldFull (N * q)) + ⟨z, hz⟩)) = ⟨y, hy⟩ + ⟨z, hz⟩
        rw [map_add, map_add, ihy, ihz]
    | inv y hy ihy =>
        show atkinLehnerInvolutionFull N q (atkinLehnerInvolutionFull N q
          ((⟨y, hy⟩ : modularFunctionFieldFull (N * q))⁻¹)) = (⟨y, hy⟩ : modularFunctionFieldFull (N * q))⁻¹
        rw [map_inv₀, map_inv₀, ihy]
    | mul y z hy hz ihy ihz =>
        show atkinLehnerInvolutionFull N q (atkinLehnerInvolutionFull N q
          ((⟨y, hy⟩ : modularFunctionFieldFull (N * q)) * ⟨z, hz⟩)) = ⟨y, hy⟩ * ⟨z, hz⟩
        rw [map_mul, map_mul, ihy, ihz]
  · rw [atkinLehnerInvolutionFull_eq_refl N q h]
    exact AlgEquiv.ext fun _ => rfl

private theorem atkinLehner_atkinLehnerBar_mul_self {N q : ℕ} [Fact q.Prime] :
    atkinLehnerBar N q * atkinLehnerBar N q = 1 := by
  unfold atkinLehnerBar
  rw [← map_mul, atkinLehner_atkinLehnerInvolutionFull_mul_self, map_one]

private theorem atkinLehner_atkinLehnerBar_apply_apply {N q : ℕ} [Fact q.Prime]
    (f : modularFunctionFieldBar (N * q)) :
    atkinLehnerBar N q (atkinLehnerBar N q f) = f := by
  rw [← AlgEquiv.mul_apply, atkinLehner_atkinLehnerBar_mul_self, AlgEquiv.one_apply]

private theorem atkinLehner_atkinLehnerBar_smul_smul {N q : ℕ} [Fact q.Prime]
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    atkinLehnerBar N q • (atkinLehnerBar N q • V) = V := by
  rw [smul_smul, atkinLehner_atkinLehnerBar_mul_self, one_smul]

private theorem atkinLehner_atkinLehnerBar_smul_injective {N q : ℕ} [Fact q.Prime] :
    Function.Injective (fun V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
      atkinLehnerBar N q • V) :=
  Function.Involutive.injective (atkinLehner_atkinLehnerBar_smul_smul (N := N) (q := q))

private theorem atkinLehner_filter_mapDomain {α : Type*} {τ : α → α} (hτ : Function.Involutive τ)
    (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] :
    (Finsupp.mapDomain τ D).filter p = Finsupp.mapDomain τ (D.filter (fun a => p (τ a))) := by
  ext a'
  obtain ⟨a, rfl⟩ : ∃ a, τ a = a' := ⟨τ a', hτ a'⟩
  by_cases hp : p (τ a)
  · simp [Finsupp.mapDomain_apply hτ.injective, hp]
  · simp [Finsupp.mapDomain_apply hτ.injective, hp]

private theorem atkinLehner_mapDomain_smul_apply {N q : ℕ} [Fact q.Prime]
    (f : modularFunctionFieldBar (N * q))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Finsupp.mapDomain (fun W => atkinLehnerBar N q • W) D V = V.ord (atkinLehnerBar N q f) := by
  obtain ⟨V₀, rfl⟩ : ∃ V₀, atkinLehnerBar N q • V₀ = V :=
    ⟨atkinLehnerBar N q • V, atkinLehner_atkinLehnerBar_smul_smul V⟩
  have h := Finsupp.mapDomain_apply (atkinLehner_atkinLehnerBar_smul_injective (N := N) (q := q)) D V₀
  rw [h, hD V₀]
  exact (Place.ord_smul (atkinLehnerBar N q) V₀ f).symm

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst reduceSnd IsStrictFst IsStrictSnd reduceFst_atkinLehnerBar_smul isStrictFst_atkinLehnerBar_smul_iff"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar IsInftySide IsZeroSide mem_integers₂_iff residue₁ residue₂ residue₁_apply residue₂_apply DivisorLawFst DivisorLawSnd CuspLawInfty CuspLawZero IsModel R₁ mem_integersFst_iff R₂ mem_integersSnd_iff residue₂_eq isInftySide_atkinLehnerBar_smul_iff"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private theorem atkinLehner_transport_mem (f : modularFunctionFieldBar (N * q))
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) :
    atkinLehnerBar N q f ∈ R.R₁.integers ∧ atkinLehnerBar N q f ∈ R.R₂.integers :=
  ⟨(R.mem_integers₂_iff f).mp h₂,
    (R.mem_integers₂_iff _).mpr (by rw [atkinLehner_atkinLehnerBar_apply_apply]; exact h₁)⟩

private theorem atkinLehner_transport_residue₁_ne_zero (f : modularFunctionFieldBar (N * q))
    (h₂ : f ∈ R.R₂.integers) (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (h₁' : atkinLehnerBar N q f ∈ R.R₁.integers) :
    R.R₁.residue ⟨atkinLehnerBar N q f, h₁'⟩ ≠ 0 := by
  rw [R.residue₂_eq f h₂] at hr₂
  exact hr₂

private theorem atkinLehner_transport_residue₂_ne_zero (f : modularFunctionFieldBar (N * q))
    (h₁ : f ∈ R.R₁.integers) (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (h₂' : atkinLehnerBar N q f ∈ R.R₂.integers) :
    R.R₂.residue ⟨atkinLehnerBar N q f, h₂'⟩ ≠ 0 := by
  rw [R.residue₂_eq _ h₂']
  have hsub : (⟨atkinLehnerBar N q (atkinLehnerBar N q f),
      (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp h₂')⟩ : R.R₁.integers)
      = ⟨f, h₁⟩ :=
    Subtype.ext (atkinLehner_atkinLehnerBar_apply_apply f)
  rw [hsub]
  exact hr₁

private theorem atkinLehner_residue₂_eq_residue₁ (f : modularFunctionFieldBar (N * q))
    (h₂ : f ∈ R.R₂.integers) (h₁' : atkinLehnerBar N q f ∈ R.R₁.integers) :
    R.residue₂ ⟨f, h₂⟩ = R.residue₁ ⟨atkinLehnerBar N q f, h₁'⟩ := by
  rw [R.residue₂_apply, R.residue₁_apply, R.residue₂_eq f h₂]

open Classical in

private theorem atkinLehner_divisorLawSnd_of_divisorLawFst (hqN : ¬ q ∣ N) (h : R.DivisorLawFst) :
    R.DivisorLawSnd := by
  intro f h₁ h₂ hr₁ hr₂ D hD v hv
  obtain ⟨h₁', h₂'⟩ := atkinLehner_transport_mem R f h₁ h₂
  have hkey := h (atkinLehnerBar N q f) h₁' h₂' (atkinLehner_transport_residue₁_ne_zero R f h₂ hr₂ h₁')
    (atkinLehner_transport_residue₂_ne_zero R f h₁ hr₁ h₂')
    (Finsupp.mapDomain (fun W => atkinLehnerBar N q • W) D) (atkinLehner_mapDomain_smul_apply f D hD)
    v hv
  have hE : D.filter (fun W => P.IsStrictFst (atkinLehnerBar N q • W)) = D.filter P.IsStrictSnd :=
    Finsupp.ext fun W => by
      by_cases hW : P.IsStrictSnd W <;>
        simp [hW, isStrictFst_atkinLehnerBar_smul_iff P hqN W]
  have hcomp : P.reduceFst ∘ (fun W => atkinLehnerBar N q • W) = P.reduceSnd :=
    funext fun W => reduceFst_atkinLehnerBar_smul P hqN W
  rw [atkinLehner_residue₂_eq_residue₁ R f h₂ h₁', ← hkey,
    atkinLehner_filter_mapDomain (atkinLehner_atkinLehnerBar_smul_smul (N := N) (q := q)), ← Finsupp.mapDomain_comp,
    hcomp]
  exact congrArg (fun E => Finsupp.mapDomain P.reduceSnd E v) hE.symm

open Classical in

private theorem atkinLehner_cuspLawZero_of_cuspLawInfty (hqN : ¬ q ∣ N) (h : R.CuspLawInfty) :
    R.CuspLawZero := by
  intro f h₁ h₂ hr₁ hr₂ D hD c hc
  obtain ⟨h₁', h₂'⟩ := atkinLehner_transport_mem R f h₁ h₂
  have hc' : IsInftySide P (atkinLehnerBar N q • c) :=
    (isInftySide_atkinLehnerBar_smul_iff P hqN c).mpr hc
  have hkey := h (atkinLehnerBar N q f) h₁' h₂' (atkinLehner_transport_residue₁_ne_zero R f h₂ hr₂ h₁')
    (atkinLehner_transport_residue₂_ne_zero R f h₁ hr₁ h₂')
    (Finsupp.mapDomain (fun W => atkinLehnerBar N q • W) D) (atkinLehner_mapDomain_smul_apply f D hD)
    (atkinLehnerBar N q • c) hc'
  have hE : D.filter (fun W => IsInftySide P (atkinLehnerBar N q • W)) = D.filter (IsZeroSide P) :=
    Finsupp.ext fun W => by
      by_cases hW : IsZeroSide P W <;>
        simp [hW, isInftySide_atkinLehnerBar_smul_iff P hqN W]
  have hcomp : P.reduceFst ∘ (fun W => atkinLehnerBar N q • W) = P.reduceSnd :=
    funext fun W => reduceFst_atkinLehnerBar_smul P hqN W
  rw [reduceFst_atkinLehnerBar_smul P hqN c] at hkey
  rw [atkinLehner_residue₂_eq_residue₁ R f h₂ h₁', ← hkey,
    atkinLehner_filter_mapDomain (atkinLehner_atkinLehnerBar_smul_smul (N := N) (q := q)), ← Finsupp.mapDomain_comp,
    hcomp]
  exact congrArg (fun E => Finsupp.mapDomain P.reduceSnd E (P.reduceSnd c)) hE.symm

private theorem atkinLehner_isModel_of_fst (hqN : ¬ q ∣ N) (h₁ : R.DivisorLawFst) (h₃ : R.CuspLawInfty) :
    R.IsModel :=
  ⟨h₁, atkinLehner_divisorLawSnd_of_divisorLawFst R hqN h₁, h₃, atkinLehner_cuspLawZero_of_cuspLawInfty R hqN h₃⟩

end ModularCurve.PlaceSpecialization.ProlongationTuple

end

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (h₁ : R.DivisorLawFst) (h₃ : R.CuspLawInfty) :
    R.IsModel :=
  ProlongationTuple.atkinLehner_isModel_of_fst R hqN h₁ h₃

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isModel_of_divisorLawFst_of_cuspLawInfty (solution)
