-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c33bc153-2734-5ab7-a6f0-9bd38dae5510

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace OneSidedWitnessSlope

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

private theorem mem_roof {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull q) :
    x ∈ modularFunctionFieldFull (N * q) :=
  full_degeneracy_le (dvd_mul_left q N) hx

private theorem coe_atkinLehner_of_mem_level
    (σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q))
    (hσ : IsAtkinLehnerAutFull N q σ)
    {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull q) :
    ((σ ⟨x, mem_roof N q hx⟩ : modularFunctionFieldFull (N * q)) : LaurentSeries ℚ) =
      ((frickeInvolutionFull q ⟨x, hx⟩ : modularFunctionFieldFull q) : LaurentSeries ℚ) := by
  have hF : IsFrickeAutFull q (frickeInvolutionFull q) := isFrickeAutFull_frickeInvolutionFull_prime q
  have hq : q.Prime := Fact.out
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨d, hd0, hd, rfl⟩ := hy
      haveI := hd0
      rcases (Nat.dvd_prime hq).mp hd with h1 | h1
      ·
        have e : (⟨qExpand ℚ d jq, mem_roof N q (jqd_mem_full q hd)⟩ :
            modularFunctionFieldFull (N * q)) =
            ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :=
          Subtype.ext (qExpand_congr h1 jq)
        have e' : (⟨qExpand ℚ d jq, jqd_mem_full q hd⟩ : modularFunctionFieldFull q) =
            ⟨qExpand ℚ 1 jq, jqd_mem_full q (Dvd.intro q (one_mul q))⟩ :=
          Subtype.ext (qExpand_congr h1 jq)
        rw [e, (hσ 1 inferInstance (one_dvd N)).1, e', hF 1 q (one_mul q) inferInstance inferInstance]
        show qExpand ℚ (1 * q) jq = qExpand ℚ q jq
        exact qExpand_congr (one_mul q) jq
      ·
        have e : (⟨qExpand ℚ d jq, mem_roof N q (jqd_mem_full q hd)⟩ :
            modularFunctionFieldFull (N * q)) =
            ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :=
          Subtype.ext (qExpand_congr (h1.trans (one_mul q).symm) jq)
        have e' : (⟨qExpand ℚ d jq, jqd_mem_full q hd⟩ : modularFunctionFieldFull q) =
            ⟨qExpand ℚ q jq, jqd_mem_full q (Dvd.intro 1 (mul_one q))⟩ :=
          Subtype.ext (qExpand_congr h1 jq)
        rw [e, (hσ 1 inferInstance (one_dvd N)).2, e', hF q 1 (mul_one q) inferInstance inferInstance]
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
          mem_roof N q ((modularFunctionFieldFull q).algebraMap_mem r)⟩ :
          modularFunctionFieldFull (N * q)) = (r : modularFunctionFieldFull (N * q)) := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r =
          ((r : modularFunctionFieldFull (N * q)) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r]
        norm_cast
      have hr' : (⟨algebraMap ℚ (LaurentSeries ℚ) r, (modularFunctionFieldFull q).algebraMap_mem r⟩ :
          modularFunctionFieldFull q) = (r : modularFunctionFieldFull q) := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r = ((r : modularFunctionFieldFull q) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r]
        norm_cast
      rw [hr, hr', map_ratCast, map_ratCast]
      norm_cast
  | add x y hx hy ihx ihy =>
      have e : (⟨x + y, mem_roof N q (add_mem hx hy)⟩ : modularFunctionFieldFull (N * q)) =
          ⟨x, mem_roof N q hx⟩ + ⟨y, mem_roof N q hy⟩ := rfl
      have e' : (⟨x + y, add_mem hx hy⟩ : modularFunctionFieldFull q) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, e', map_add, map_add, IntermediateField.coe_add, IntermediateField.coe_add, ihx, ihy]
  | inv x hx ih =>
      have e : (⟨x⁻¹, mem_roof N q (inv_mem hx)⟩ : modularFunctionFieldFull (N * q)) =
          (⟨x, mem_roof N q hx⟩)⁻¹ := rfl
      have e' : (⟨x⁻¹, inv_mem hx⟩ : modularFunctionFieldFull q) = (⟨x, hx⟩)⁻¹ := rfl
      rw [e, e', map_inv₀, map_inv₀, IntermediateField.coe_inv, IntermediateField.coe_inv, ih]
  | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mem_roof N q (mul_mem hx hy)⟩ : modularFunctionFieldFull (N * q)) =
          ⟨x, mem_roof N q hx⟩ * ⟨y, mem_roof N q hy⟩ := rfl
      have e' : (⟨x * y, mul_mem hx hy⟩ : modularFunctionFieldFull q) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, e', map_mul, map_mul, IntermediateField.coe_mul, IntermediateField.coe_mul, ihx, ihy]

private theorem modularUnitSeries_mul_coe_atkinLehnerInvolutionFull (hqN : ¬ q ∣ N) :
    modularUnitSeries q *
      ((atkinLehnerInvolutionFull N q
          ⟨modularUnitSeries q, mem_roof N q (modularUnitSeries_mem_modularFunctionFieldFull q)⟩ :
          modularFunctionFieldFull (N * q)) : LaurentSeries ℚ) =
      ((q : ℕ) : LaurentSeries ℚ) ^ 12 := by
  have hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  rw [coe_atkinLehner_of_mem_level N q _ hAL (modularUnitSeries_mem_modularFunctionFieldFull q),
    coe_frickeInvolutionFull_modularUnitSeries q (modularUnitSeries_mem_modularFunctionFieldFull q),
    ← HahnSeries.C_mul_eq_smul, mul_left_comm, mul_inv_cancel₀ (modularUnitSeries_ne_zero q), mul_one,
    map_pow, map_natCast]

end OneSidedWitnessSlope

end

set_option maxHeartbeats 3200000 in
open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple AlgebraicCurve IsLocalRing OneSidedWitnessSlope in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers) (hres₁ : R.R₁.residue ⟨u, h₁⟩ ≠ 0) :
    ∀ h₂ : u ∈ R.R₂.integers, R.R₂.residue ⟨u, h₂⟩ = 0 := by
  intro h₂

  rw [R.residue₂_eq u h₂]
  have hw₁ : ProlongationTuple.atkinLehnerBar N q u ∈ R.R₁.integers :=
    (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff u).mp h₂)

  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N * q) :=
    mem_roof N q (modularUnitSeries_mem_modularFunctionFieldFull q)
  have hu' : u = ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ := Subtype.ext hu
  have hcoe_w : ((ProlongationTuple.atkinLehnerBar N q u : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ)
        ((atkinLehnerInvolutionFull N q ⟨modularUnitSeries q, hmem⟩ :
          modularFunctionFieldFull (N * q)) : LaurentSeries ℚ) := by
    rw [hu']
    exact coe_geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
      (atkinLehnerInvolutionFull N q) ⟨modularUnitSeries q, hmem⟩
  have hprod : (u : LaurentSeries (AlgebraicClosure ℚ)) *
      ((ProlongationTuple.atkinLehnerBar N q u : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ((q : ℕ) : LaurentSeries (AlgebraicClosure ℚ)) ^ 12 := by
    rw [hcoe_w, hu, ← map_mul, modularUnitSeries_mul_coe_atkinLehnerInvolutionFull N q hqN, map_pow,
      map_natCast]
  have hprodBar : u * ProlongationTuple.atkinLehnerBar N q u =
      ((q : ℕ) : modularFunctionFieldBar (N * q)) ^ 12 := by
    apply Subtype.ext
    rw [IntermediateField.coe_mul, hprod]
    norm_cast

  have hint : (⟨u, h₁⟩ : R.R₁.integers) * ⟨ProlongationTuple.atkinLehnerBar N q u, hw₁⟩ =
      ((q : ℕ) : R.R₁.integers) ^ 12 := by
    apply Subtype.ext
    show u * ProlongationTuple.atkinLehnerBar N q u =
      (((((q : ℕ) : R.R₁.integers) ^ 12 : R.R₁.integers)) : modularFunctionFieldBar (N * q))
    rw [hprodBar]
    norm_cast

  have hqmax : ((q : ℕ) : A) ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h0 : red ((q : ℕ) : A) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
    exact (hunit.map red).ne_zero h0
  have hqres : ((q : ℕ) : modularFunctionFieldFullC (ResidueField A) N) = 0 := by
    rw [← map_natCast (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)),
      ← map_natCast (IsLocalRing.residue A), (IsLocalRing.residue_eq_zero_iff _).mpr hqmax, map_zero]
  have hzero : R.R₁.residue ⟨u, h₁⟩ * R.R₁.residue ⟨ProlongationTuple.atkinLehnerBar N q u, hw₁⟩ = 0 := by
    rw [← map_mul, hint, map_pow, map_natCast, hqres, zero_pow (by norm_num)]

  exact (mul_eq_zero.mp hzero).resolve_left hres₁

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries (solution)
