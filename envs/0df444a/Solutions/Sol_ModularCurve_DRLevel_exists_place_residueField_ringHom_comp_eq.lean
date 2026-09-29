-- Prove2me | solution 1 for ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/780503a3-d5eb-5da7-b262-f16ea133b46a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq.ModularCurve.DRLevel IsLocalRing"
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R IgusaScheme"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R"
namespace PlaceCover
p2m_open "ModularCurve.DRLevel ModularCurve"

private theorem ringHom_ext {q : ℕ} {S : Type} [Ring S] (f g : DRLevel.R q →+* S) : f = g := by
  apply RingHom.ext
  intro x
  set d : ℕ := (x : ℚ).den with hd
  have hd0 : d ≠ 0 := (x : ℚ).den_nz
  have hmem : ((d : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt q := by
    show (((d : ℚ))⁻¹).den.Coprime q
    rw [Rat.inv_natCast_den, if_neg hd0]
    exact x.2
  let D : DRLevel.R q := ⟨(d : ℚ), by
    show ((d : ℚ)).den.Coprime q
    rw [Rat.den_natCast]; exact Nat.coprime_one_left q⟩
  let Di : DRLevel.R q := ⟨((d : ℚ))⁻¹, hmem⟩
  have hDnat : D = (d : DRLevel.R q) := Subtype.ext (by simp [D])
  have hDDi : D * Di = 1 := Subtype.ext (by
    show (d : ℚ) * ((d : ℚ))⁻¹ = 1
    exact mul_inv_cancel₀ (by exact_mod_cast hd0))
  have hDiD : Di * D = 1 := by rw [mul_comm]; exact hDDi
  have hxD : x * D = ((x : ℚ).num : DRLevel.R q) := Subtype.ext (by
    show (x : ℚ) * (d : ℚ) = (((x : ℚ).num : ℤ) : ℚ)
    exact_mod_cast Rat.mul_den_eq_num (x : ℚ))

  have hfD : f D = (d : S) := by rw [hDnat, map_natCast]
  have hgD : g D = (d : S) := by rw [hDnat, map_natCast]
  have hinv : f Di = g Di := by
    have h1 : f Di * (d : S) = 1 := by rw [← hfD, ← map_mul, hDiD, map_one]
    have h2 : (d : S) * g Di = 1 := by rw [← hgD, ← map_mul, hDDi, map_one]
    calc f Di = f Di * ((d : S) * g Di) := by rw [h2, mul_one]
      _ = (f Di * (d : S)) * g Di := by rw [mul_assoc]
      _ = g Di := by rw [h1, one_mul]
  have hx : x = ((x : ℚ).num : DRLevel.R q) * Di := by
    rw [← hxD, mul_assoc, hDDi, mul_one]
  rw [hx, map_mul, map_mul, map_intCast, map_intCast, hinv]

private theorem isAlgebraic_residueField {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [Algebra (ZMod q) (ResidueField ↥A)] :
    Algebra.IsAlgebraic (ZMod q) (ResidueField ↥A) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  have hx : residue ↥A a = x := ha
  rw [← hx]

  have ha : IsAlgebraic ℚ (a : AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isAlgebraic _
  have haℤ : IsAlgebraic ℤ (a : AlgebraicClosure ℚ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr ha
  obtain ⟨p, hp0, hpa⟩ := haℤ
  set r := p.primPart with hr
  have hr_prim : r.IsPrimitive := p.isPrimitive_primPart
  have hra : Polynomial.aeval (a : AlgebraicClosure ℚ) r = 0 := by
    have hc : p.content ≠ 0 := fun h => hp0 (Polynomial.content_eq_zero_iff.mp h)
    have h := hpa
    rw [p.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (by simpa [algebraMap_int_eq] using h1) hc
    · exact h1

  refine ⟨r.map (Int.castRingHom (ZMod q)), ?_, ?_⟩
  · intro h0
    have hdvd : Polynomial.C (q : ℤ) ∣ r := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi : (r.map (Int.castRingHom (ZMod q))).coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [Polynomial.coeff_map] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hi
    have hu := hr_prim (q : ℤ) hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact (Fact.out : q.Prime).ne_one hu
  ·
    have h1 : Polynomial.aeval (residue ↥A a) (r.map (Int.castRingHom (ZMod q))) =
        Polynomial.aeval (residue ↥A a) r := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]
      congr 1
      exact RingHom.ext_int _ _
    rw [h1]
    have h2 : Polynomial.aeval (residue ↥A a) r = (residue ↥A) (Polynomial.aeval a r) := by
      rw [← RingHom.toIntAlgHom_apply (residue ↥A) a, Polynomial.aeval_algHom_apply]
      rfl
    rw [h2]
    have h3 : Polynomial.aeval a r = 0 := by
      have hinj : Function.Injective (A.subtype.toIntAlgHom) := Subtype.val_injective
      apply hinj
      rw [map_zero, ← Polynomial.aeval_algHom_apply]
      convert hra using 2
      rfl
    rw [h3, map_zero]

end ModularCurve.DRLevel.PlaceCover

open ModularCurve.DRLevel.PlaceCover in
theorem solution
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] (toκ : DRLevel.R q →+* κ) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime q)
      (_ : CharP (ResidueField ↥A) q) (_ : IsAlgClosed (ResidueField ↥A))
      (ρ : DRLevel.R q →+* ↥A) (_ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
      (φ : ResidueField ↥A →+* κ), φ.comp ((residue ↥A).comp ρ) = toκ := by
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨q, Fact.out⟩
  obtain ⟨ρ, hρ⟩ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime q A hA
  haveI hchar : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime q A hA
  haveI halg : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  letI : Algebra (ZMod q) (ResidueField ↥A) := ZMod.algebra _ q
  letI : Algebra (ZMod q) κ := ZMod.algebra _ q
  haveI : Algebra.IsAlgebraic (ZMod q) (ResidueField ↥A) := isAlgebraic_residueField A
  let e : ResidueField ↥A →ₐ[ZMod q] κ := IsAlgClosed.lift
  exact ⟨A, hA, hchar, halg, ρ, hρ, e.toRingHom, ModularCurve.DRLevel.PlaceCover.ringHom_ext _ _⟩
end

end S_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq
end P2MW
export P2MW.S_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq (solution)
