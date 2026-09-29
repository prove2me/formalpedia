-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_levelOneProlongationPair_of_prolongationTuple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c1109e97-1c48-5338-8aef-2514453d3af7

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple.ModularCurve ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand jq ModularPolynomialData modularFunctionFieldFull jqd_mem_full PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl frickeInvolutionBar frickeInvolutionBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull frickeInvolutionFull_eq_refl geomAut"
p2m_open "ModularCurve"

theorem mk_qExpand_congr (M : ℕ) {d e : ℕ} [NeZero d] [NeZero e] (hde : d = e)
    (hd : qExpand ℚ d jq ∈ modularFunctionFieldFull M) (he : qExpand ℚ e jq ∈ modularFunctionFieldFull M) :
    (⟨qExpand ℚ d jq, hd⟩ : modularFunctionFieldFull M) = ⟨qExpand ℚ e jq, he⟩ := by
  subst hde
  rfl

theorem algEquiv_modularFunctionFieldFull_ext (M : ℕ)
    (σ τ : modularFunctionFieldFull M ≃ₐ[ℚ] modularFunctionFieldFull M)
    (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ M),
      σ ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩ = τ ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩) :
    σ = τ := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  suffices hmain : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull M),
      ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) = (τ ⟨y, hy⟩ : modularFunctionFieldFull M) from
    Subtype.ext (hmain x hx)
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hd0, hdM, rfl⟩ := hy
    exact congrArg Subtype.val (h d hd0 hdM)
  | algebraMap r =>

    have e : (⟨_, IntermediateField.algebraMap_mem (modularFunctionFieldFull M) r⟩ : modularFunctionFieldFull M)
        = ((r : ℚ) : modularFunctionFieldFull M) := by
      apply Subtype.ext
      rw [SubfieldClass.coe_ratCast]
      exact eq_ratCast _ r
    rw [e, map_ratCast, map_ratCast]
  | add y z hy hz ihy ihz =>
    have e : (⟨y + z, add_mem hy hz⟩ : modularFunctionFieldFull M) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [e, map_add, map_add]
    show ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) + (σ ⟨z, hz⟩ : modularFunctionFieldFull M)
      = ((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) + (τ ⟨z, hz⟩ : modularFunctionFieldFull M)
    rw [ihy, ihz]
  | inv y hy ihy =>
    have e : (⟨y⁻¹, inv_mem hy⟩ : modularFunctionFieldFull M) = (⟨y, hy⟩ : modularFunctionFieldFull M)⁻¹ := rfl
    rw [e, map_inv₀, map_inv₀]
    show (((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ))⁻¹
      = (((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ))⁻¹
    rw [ihy]
  | mul y z hy hz ihy ihz =>
    have e : (⟨y * z, mul_mem hy hz⟩ : modularFunctionFieldFull M) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e, map_mul, map_mul]
    show ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) * (σ ⟨z, hz⟩ : modularFunctionFieldFull M)
      = ((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) * (τ ⟨z, hz⟩ : modularFunctionFieldFull M)
    rw [ihy, ihz]

theorem isAtkinLehnerAutFull_one_iff (q : ℕ) [Fact q.Prime]
    (σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    IsAtkinLehnerAutFull 1 q σ ↔ IsFrickeAutFull (1 * q) σ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : q.Prime := Fact.out
  constructor
  · intro hAL a b hab ha hb
    obtain ⟨h1, h2⟩ := hAL 1 inferInstance (dvd_refl 1)

    have ha' : a ∣ q := ⟨b, by omega⟩
    rcases (Nat.dvd_prime hq).mp ha' with ha1 | haq
    · have hb' : b = 1 * q := by rw [ha1] at hab; omega
      rw [mk_qExpand_congr (1 * q) ha1 _ (jqd_mem_full (1 * q) (one_dvd _)),
        mk_qExpand_congr (1 * q) hb' _ (jqd_mem_full (1 * q) (dvd_refl _))]
      exact h1
    · have hb' : b = 1 := by
        have : q * b = q * 1 := by rw [haq] at hab; rw [mul_one, hab, one_mul]
        exact Nat.eq_of_mul_eq_mul_left hq.pos this
      rw [mk_qExpand_congr (1 * q) (haq.trans (one_mul q).symm) _ (jqd_mem_full (1 * q) (dvd_refl _)),
        mk_qExpand_congr (1 * q) hb' _ (jqd_mem_full (1 * q) (one_dvd _))]
      exact h2
  · intro hF d hd0 hd
    obtain rfl : d = 1 := Nat.dvd_one.mp hd
    constructor
    · exact hF 1 (1 * q) (by ring) inferInstance inferInstance
    · exact hF (1 * q) 1 (by ring) inferInstance inferInstance

theorem atkinLehnerInvolutionFull_one (q : ℕ) [Fact q.Prime] :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    atkinLehnerInvolutionFull 1 q = frickeInvolutionFull (1 * q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : q.Prime := Fact.out
  by_cases hex : ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
      IsFrickeAutFull (1 * q) σ
  · have hex' : ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
        IsAtkinLehnerAutFull 1 q σ := by
      obtain ⟨σ, hσ⟩ := hex
      exact ⟨σ, (isAtkinLehnerAutFull_one_iff q σ).mpr hσ⟩
    have h1 := (isAtkinLehnerAutFull_one_iff q _).mp (isAtkinLehnerAutFull_atkinLehnerInvolutionFull 1 q hex')
    have h2 := isFrickeAutFull_frickeInvolutionFull (1 * q) hex
    apply algEquiv_modularFunctionFieldFull_ext
    intro d hd0 hd
    have hd' : d ∣ q := by rwa [one_mul] at hd
    rcases (Nat.dvd_prime hq).mp hd' with hd1 | hdq
    · have e1 := h1 1 (1 * q) (by ring) inferInstance inferInstance
      have e2 := h2 1 (1 * q) (by ring) inferInstance inferInstance
      rw [mk_qExpand_congr (1 * q) hd1 _ (jqd_mem_full (1 * q) (one_dvd _))]
      exact e1.trans e2.symm
    · have e1 := h1 (1 * q) 1 (by ring) inferInstance inferInstance
      have e2 := h2 (1 * q) 1 (by ring) inferInstance inferInstance
      rw [mk_qExpand_congr (1 * q) (hdq.trans (one_mul q).symm) _ (jqd_mem_full (1 * q) (dvd_refl _))]
      exact e1.trans e2.symm
  · have hex' : ¬ ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
        IsAtkinLehnerAutFull 1 q σ := fun ⟨σ, hσ⟩ => hex ⟨σ, (isAtkinLehnerAutFull_one_iff q σ).mp hσ⟩
    rw [atkinLehnerInvolutionFull_eq_refl 1 q hex', frickeInvolutionFull_eq_refl (1 * q) hex]

theorem atkinLehnerBar_one (q : ℕ) [Fact q.Prime] :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  show geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q)) (atkinLehnerInvolutionFull 1 q) = _
  rw [frickeInvolutionBar_def, atkinLehnerInvolutionFull_one]

end ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) :
    ∃ R' : P.LevelOneProlongationPair, R'.R₁ = R.R₁ ∧ R'.R₂ = R.R₂ := by
  have hw : ∀ f : modularFunctionFieldBar (1 * q),
      ProlongationTuple.atkinLehnerBar 1 q f = frickeInvolutionBar (1 * q) f := fun f => by
    rw [atkinLehnerBar_one]
  refine ⟨{ redBar := R.redBar
            redBar_residue := R.redBar_residue
            ι := R.ι
            ι_coe := R.ι_coe
            R₁ := R.R₁
            R₂ := R.R₂
            residue₁_coeffMap := R.residue₁_coeffMap
            mem_integers₂_iff := fun f => by rw [R.mem_integers₂_iff, hw]
            residue₂_eq := fun f h => by
              rw [R.residue₂_eq f h]
              congr 1
              exact Subtype.ext (hw f)
            residue₁_eq_modularRedLocHom := R.residue₁_eq_modularRedLocHom }, rfl, rfl⟩

end S_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple (solution)
