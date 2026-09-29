-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8284e3c8-376d-517c-9b38-3c578719988f

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open ModularCurve ModularCurve.NodeLocalized IsLocalRing

namespace KPRIMELIFT

variable {p : ℕ} [Fact p.Prime] {Ab : ValuationSubring (AlgebraicClosure ℚ)}

theorem charP_residueField (hAb : Ab.LiesOverPrime p) : CharP (ResidueField ↥Ab) p := by
  have h0 : IsLocalRing.residue ↥Ab ((p : ℕ) : ↥Ab) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    simp at hAb ⊢
    exact hAb
  rw [map_natCast] at h0
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

omit [Fact p.Prime] in
theorem hker : ∀ c : ↥Ab, IsLocalRing.residue ↥Ab c = 0 ↔ c ∈ maximalIdeal ↥Ab :=
  fun _ => IsLocalRing.residue_eq_zero_iff _

omit [Fact p.Prime] in

theorem redRestrict_eq_zero_iff_not_isUnit (K' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (d : ↥(coeffSubring Ab K')) :
    redRestrict (IsLocalRing.residue ↥Ab) K' d = 0 ↔ ¬ IsUnit d := by
  let f : ↥(coeffSubring Ab K') →+* ↥Ab := (Subring.inclusion (inf_le_left : coeffSubring Ab K' ≤ Ab.toSubring))
  change IsLocalRing.residue ↥Ab (f d) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h hu
    exact (IsLocalRing.mem_maximalIdeal _).mp h (hu.map f)
  · intro h
    by_contra hmem
    apply h
    have hu : IsUnit (f d) := not_not.mp (mt (IsLocalRing.mem_maximalIdeal _).mpr hmem)
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : ((d : AlgebraicClosure ℚ)) * (w : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : ↥Ab => (z : AlgebraicClosure ℚ)) hw
      simp [f] at this
      exact this
    have hwinv : (w : AlgebraicClosure ℚ) = ((d : AlgebraicClosure ℚ))⁻¹ := eq_inv_of_mul_eq_one_right hw'
    have hwK : (w : AlgebraicClosure ℚ) ∈ coeffSubring Ab K' := by
      refine ⟨w.2, ?_⟩
      rw [hwinv]
      exact K'.inv_mem d.2.2
    exact IsUnit.of_mul_eq_one ⟨(w : AlgebraicClosure ℚ), hwK⟩ (Subtype.ext hw')

theorem main (hAb : Ab.LiesOverPrime p)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (ϖb : ↥(coeffSubring Ab K))
    (hϖb : ∀ d : ↥(coeffSubring Ab K), redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
    (e₀ : ℕ) (ε : ↥(coeffSubring Ab K)) (hε : IsUnit ε)
    (hpε : ((p : ℕ) : ↥(coeffSubring Ab K)) = ϖb ^ e₀ * ε)
    (j₀ : IsLocalRing.ResidueField ↥Ab) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K') (_ : K ≤ K')
      (xw : ↥(coeffSubring Ab K')) (_ : redRestrict (IsLocalRing.residue ↥Ab) K' xw = j₀)
      (ϖ' : ↥(coeffSubring Ab K'))
      (_ : ∀ d : ↥(coeffSubring Ab K'), redRestrict (IsLocalRing.residue ↥Ab) K' d = 0 ↔ ∃ d', d = ϖ' * d')
      (r : ℕ) (_ : 1 ≤ r) (u : ↥(coeffSubring Ab K')) (_ : IsUnit u)
      (_ : (ϖb : AlgebraicClosure ℚ) = ((ϖ' ^ r * u : ↥(coeffSubring Ab K')) : AlgebraicClosure ℚ))
      (ε' : ↥(coeffSubring Ab K')) (_ : IsUnit ε'),
      ((p : ℕ) : ↥(coeffSubring Ab K')) = ϖ' ^ (r * e₀) * ε' := by
  haveI : CharP (ResidueField ↥Ab) p := charP_residueField hAb

  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective j₀
  obtain ⟨K₀, hK₀fd, -, x, hx⟩ :=
    ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level Ab (IsLocalRing.residue ↥Ab) j₀
      ⟨y, hy⟩ 1 (1 : ↥(modularFunctionFieldBar 1))
  haveI := hK₀fd
  let K' : IntermediateField ℚ (AlgebraicClosure ℚ) := K ⊔ K₀
  haveI : FiniteDimensional ℚ ↥K' := IntermediateField.finiteDimensional_sup K K₀
  have hKK' : K ≤ K' := le_sup_left
  have hsub : coeffSubring Ab K ≤ coeffSubring Ab K' := fun z hz => ⟨hz.1, hKK' hz.2⟩
  have hsub₀ : coeffSubring Ab K₀ ≤ coeffSubring Ab K' := fun z hz => ⟨hz.1, (le_sup_right : K₀ ≤ K') hz.2⟩
  let ι : ↥(coeffSubring Ab K) →+* ↥(coeffSubring Ab K') := Subring.inclusion hsub

  let xw : ↥(coeffSubring Ab K') := Subring.inclusion hsub₀ x
  have hxw : redRestrict (IsLocalRing.residue ↥Ab) K' xw = j₀ := hx

  haveI : IsDiscreteValuationRing ↥(coeffSubring Ab K') :=
    ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring (IsLocalRing.residue ↥Ab) hker K'
  obtain ⟨ϖ', hϖ', -⟩ :=
    ModularCurve.NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
      (IsLocalRing.residue ↥Ab) hker K'
  have hmax : maximalIdeal ↥(coeffSubring Ab K') = Ideal.span {ϖ'} := by
    ext z
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← redRestrict_eq_zero_iff_not_isUnit, hϖ',
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨d', rfl⟩; exact ⟨d', mul_comm _ _⟩
    · rintro ⟨d', rfl⟩; exact ⟨d', mul_comm _ _⟩
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_zero] at hmax
    exact IsDiscreteValuationRing.not_a_field ↥(coeffSubring Ab K') hmax
  have hirr : Irreducible ϖ' := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ' hϖ'0 hmax

  have hϖbK : redRestrict (IsLocalRing.residue ↥Ab) K ϖb = 0 := (hϖb ϖb).mpr ⟨1, (mul_one _).symm⟩
  have hϖb0 : ϖb ≠ 0 := by
    intro h0
    have hpK : redRestrict (IsLocalRing.residue ↥Ab) K ((p : ℕ) : ↥(coeffSubring Ab K)) = 0 := by
      rw [map_natCast]
      exact CharP.cast_eq_zero _ p
    obtain ⟨d', hd'⟩ := (hϖb _).mp hpK
    rw [h0, zero_mul] at hd'
    have : ((p : ℕ) : AlgebraicClosure ℚ) = 0 := by
      have := congrArg (fun z : ↥(coeffSubring Ab K) => (z : AlgebraicClosure ℚ)) hd'
      simpa using this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have hιϖb0 : ι ϖb ≠ 0 := fun h => hϖb0 (Subring.inclusion_injective hsub (h.trans (map_zero _).symm))
  have hιϖb_red : redRestrict (IsLocalRing.residue ↥Ab) K' (ι ϖb) = 0 := hϖbK
  have hιϖb_nu : ¬ IsUnit (ι ϖb) := (redRestrict_eq_zero_iff_not_isUnit K' _).mp hιϖb_red

  obtain ⟨r, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hιϖb0 hirr
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hru
      exact hιϖb_nu (hru ▸ Units.isUnit u)
    · exact h

  have hpK' : ((p : ℕ) : ↥(coeffSubring Ab K')) = ϖ' ^ (r * e₀) * ((u : ↥(coeffSubring Ab K')) ^ e₀ * ι ε) := by
    have h := congrArg ι hpε
    rw [map_natCast, map_mul, map_pow, hru] at h
    rw [h]
    ring
  refine ⟨K', inferInstance, hKK', xw, hxw, ϖ', hϖ', r, hr, (u : ↥(coeffSubring Ab K')), Units.isUnit u, ?_,
    (u : ↥(coeffSubring Ab K')) ^ e₀ * ι ε, (Units.isUnit u).pow e₀ |>.mul (hε.map ι), hpK'⟩
  have : (ι ϖb : ↥(coeffSubring Ab K')) = ϖ' ^ r * u := by rw [hru, mul_comm]
  exact congrArg (fun z : ↥(coeffSubring Ab K') => (z : AlgebraicClosure ℚ)) this

end KPRIMELIFT

end

open ModularCurve ModularCurve.NodeLocalized

theorem solution
    (p : ℕ) [Fact p.Prime] (Ab : ValuationSubring (AlgebraicClosure ℚ)) (hAb : Ab.LiesOverPrime p)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (ϖb : ↥(coeffSubring Ab K))
    (hϖb : ∀ d : ↥(coeffSubring Ab K), redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
    (e₀ : ℕ) (ε : ↥(coeffSubring Ab K)) (hε : IsUnit ε)
    (hpε : ((p : ℕ) : ↥(coeffSubring Ab K)) = ϖb ^ e₀ * ε)
    (j₀ : IsLocalRing.ResidueField ↥Ab) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K') (_ : K ≤ K')
      (xw : ↥(coeffSubring Ab K')) (_ : redRestrict (IsLocalRing.residue ↥Ab) K' xw = j₀)
      (ϖ' : ↥(coeffSubring Ab K'))
      (_ : ∀ d : ↥(coeffSubring Ab K'), redRestrict (IsLocalRing.residue ↥Ab) K' d = 0 ↔ ∃ d', d = ϖ' * d')
      (r : ℕ) (_ : 1 ≤ r) (u : ↥(coeffSubring Ab K')) (_ : IsUnit u)
      (_ : (ϖb : AlgebraicClosure ℚ) = ((ϖ' ^ r * u : ↥(coeffSubring Ab K')) : AlgebraicClosure ℚ))
      (ε' : ↥(coeffSubring Ab K')) (_ : IsUnit ε'),
      ((p : ℕ) : ↥(coeffSubring Ab K')) = ϖ' ^ (r * e₀) * ε' :=
  KPRIMELIFT.main hAb K ϖb hϖb e₀ ε hε hpε j₀

end S_ModularCurve_NodeLocalized_exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_le_redRestrict_eq_and_forall_redRestrict_eq_zero_iff_and_eq_pow_mul_coeffSubring_of_liesOverPrime (solution)
