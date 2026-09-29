-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c90a86dc-2ad0-5dbf-b760-a9c0e811101b

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHPlaceSpecialization_sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt.ModularCurve"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.ΓN JHNeronObjectAtP.Fbar JHNeronObjectAtP arithmeticGalois coe_arithmeticGalois_smul coeffMap coeffMap_coeffMap coeffMap_id infSubgroup xHFunctionField xHFunctionFieldBar qExpFrobeniusPlaceModL qExpArithFrobC coe_qExpArithFrobC_smul qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul"
namespace PlaceSpecHGaloisProof
p2m_open "ModularCurve"

theorem coeffMap_ne_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {x : LaurentSeries R} (hx : x ≠ 0) : coeffMap φ x ≠ 0 := by
  intro h
  apply hx
  ext k
  have hk : φ (x.coeff k) = φ 0 := by
    have := congrArg (fun z : LaurentSeries S => z.coeff k) h
    simpa using this
  simpa using hφ hk

theorem mapDomain_smul_apply_eq_ord {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (f : F) (D : Divisor K F) (hD : ∀ P, D P = P.ord f) (Q : Place K F) :
    Finsupp.mapDomain (fun P => g • P) D Q = Q.ord (g • f) := by
  have hQ : Q = g • (g⁻¹ • Q) := (smul_inv_smul g Q).symm
  rw [hQ, Finsupp.mapDomain_apply (MulAction.injective g), hD, SemilinearAut.ord_smul]

theorem mapDomain_inv_smul_apply {K F : Type*} [Field K] [Field F] [Algebra K F]
    (C : SemilinearAut K F) (X : Divisor K F) (Q : Place K F) :
    Finsupp.mapDomain (fun v => C⁻¹ • v) X Q = X (C • Q) := by
  conv_lhs => rw [← inv_smul_smul C Q]
  exact Finsupp.mapDomain_apply (MulAction.injective C⁻¹) X (C • Q)

section Decomposition

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)

theorem exists_ringHom_of_mem_decompositionSubgroup (d : ↥(A.decompositionSubgroup ℚ))
    (τ : ResidueField ↥A →+* ResidueField ↥A) (hd : ∀ x : ResidueField ↥A, d • x = τ x) :
    ∃ τA : ↥A →+* ↥A,
      A.subtype.comp τA = ((d : L ≃ₐ[ℚ] L) : L →+* L).comp A.subtype ∧
      (IsLocalRing.residue ↥A).comp τA = τ.comp (IsLocalRing.residue ↥A) := by
  refine ⟨MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) ↥A d, RingHom.ext fun a => rfl,
    RingHom.ext fun a => ?_⟩
  simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, IsLocalRing.ResidueField.residue_smul, hd]

end Decomposition

section Residue

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (FL : IntermediateField L (LaurentSeries L))
variable (Fb : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))

theorem residue_smul_of_coeff_laws
    (R : RegularProlongation A ↥FL ↥Fb)
    (hgauss : ∀ f : ↥FL, f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥FL) : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
      (((f : R.integers) : ↥FL) : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x →
      ((R.residue f : ↥Fb) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y =
        coeffMap (IsLocalRing.residue ↥A) x)
    (g : SemilinearAut L ↥FL) (σL : L →+* L)
    (hg : ∀ x : ↥FL, ((g • x : ↥FL) : LaurentSeries L) = coeffMap σL (x : LaurentSeries L))
    (τA : ↥A →+* ↥A) (hsub : A.subtype.comp τA = σL.comp A.subtype)
    (τ : ResidueField ↥A →+* ResidueField ↥A)
    (hresτ : (IsLocalRing.residue ↥A).comp τA = τ.comp (IsLocalRing.residue ↥A))
    (C : SemilinearAut (ResidueField ↥A) ↥Fb)
    (hC : ∀ y : ↥Fb, ((C • y : ↥Fb) : LaurentSeries (ResidueField ↥A)) = coeffMap τ (y : LaurentSeries (ResidueField ↥A)))
    (f : ↥FL) (hf : f ∈ R.integers) :
    ∃ hgf : g • f ∈ R.integers, R.residue ⟨g • f, hgf⟩ = C • R.residue ⟨f, hf⟩ := by
  have hι : ∀ y : LaurentSeries ↥A,
      coeffMap A.subtype (coeffMap τA y) = coeffMap σL (coeffMap A.subtype y) := by
    intro y; rw [coeffMap_coeffMap, coeffMap_coeffMap, hsub]
  have hϖ : ∀ y : LaurentSeries ↥A,
      coeffMap (IsLocalRing.residue ↥A) (coeffMap τA y) = coeffMap τ (coeffMap (IsLocalRing.residue ↥A) y) := by
    intro y; rw [coeffMap_coeffMap, coeffMap_coeffMap, hresτ]
  have hτinj : Function.Injective τ := τ.injective
  have hh := (hgauss f).mp hf
  obtain ⟨x, y, hy, hxy⟩ := hh
  have hyσ : coeffMap (IsLocalRing.residue ↥A) (coeffMap τA y) ≠ 0 := by
    rw [hϖ]; exact coeffMap_ne_zero τ hτinj hy
  have hxyσ : ((g • f : ↥FL) : LaurentSeries L) * coeffMap A.subtype (coeffMap τA y) = coeffMap A.subtype (coeffMap τA x) := by
    rw [hι, hι, hg, ← map_mul, hxy]

  have hgf : g • f ∈ R.integers := (hgauss (g • f)).mpr ⟨coeffMap τA x, coeffMap τA y, hyσ, hxyσ⟩
  refine ⟨hgf, ?_⟩

  have h1 := hres ⟨f, hf⟩ x y hy hxy
  have h2 := hres ⟨g • f, hgf⟩ (coeffMap τA x) (coeffMap τA y) hyσ hxyσ
  rw [hϖ, hϖ, ← h1, map_mul] at h2
  have h3 := mul_right_cancel₀ (coeffMap_ne_zero τ hτinj hy) h2
  exact Subtype.ext (h3.trans (hC _).symm)

end Residue

section Places

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fb : Type*) [Field Fb] [Algebra (ResidueField ↥A) Fb]

theorem sp_smul_of_residue_smul
    (R : RegularProlongation A F Fb) (sp : Place L F → Place (ResidueField ↥A) Fb)
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f))
    (huniq : ∀ sp' : Place L F → Place (ResidueField ↥A) Fb,
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp)
    (g : SemilinearAut L F) (C : SemilinearAut (ResidueField ↥A) Fb)
    (hgC : ∀ (f : F) (hf : f ∈ R.integers), ∃ hgf : g • f ∈ R.integers, R.residue ⟨g • f, hgf⟩ = C • R.residue ⟨f, hf⟩)
    (w : Place L F) :
    sp (g • w) = C • sp w := by
  have hkey : (fun v => C⁻¹ • v) ∘ sp ∘ (fun P : Place L F => g • P) = sp := by
    refine huniq _ ?_
    intro f hf0 D hD Q
    obtain ⟨f, hf⟩ := f
    obtain ⟨hgf, hresg⟩ := hgC f hf
    have hres0 := (smul_ne_zero_iff_ne C).mpr hf0
    rw [← hresg] at hres0
    rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp, mapDomain_inv_smul_apply,
      hdiv ⟨g • f, hgf⟩ hres0 (Finsupp.mapDomain (fun P => g • P) D) (mapDomain_smul_apply_eq_ord g f D hD) (C • Q),
      hresg, SemilinearAut.ord_smul]
  have hw := congrFun hkey w
  simp only [Function.comp_apply] at hw
  rw [← hw, smul_inv_smul]

end Places

end ModularCurve.PlaceSpecHGaloisProof

open ModularCurve.PlaceSpecHGaloisProof in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (hgauss : ∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (hres : ∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
      (((f : R.integers) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
      ((R.residue f : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y =
        coeffMap (IsLocalRing.residue ↥A) x)

    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
        ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f))

    (huniq : ∀ sp' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
          ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp) :
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) = sp w) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (sp w)) := by

  have main : ∀ (d : ↥(A.decompositionSubgroup ℚ)) (τ : ResidueField ↥A →+* ResidueField ↥A),
      (∀ x : ResidueField ↥A, d • x = τ x) →
      ∀ C : SemilinearAut (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
        (∀ y : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A),
          ((C • y : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
            coeffMap τ (y : LaurentSeries (ResidueField ↥A))) →
        ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
          sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM))
              (d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • w) = C • sp w := by
    intro d τ hd C hC w
    obtain ⟨τA, hsub, hresτ⟩ := exists_ringHom_of_mem_decompositionSubgroup A d τ hd
    exact sp_smul_of_residue_smul A _ _ R sp hdiv huniq _ C
      (fun f hf => residue_smul_of_coeff_laws A _ _ R hgauss hres _ _
        (coe_arithmeticGalois_smul (xHFunctionField (M / p) (infSubgroup p M H hpM)) (d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
        τA hsub τ hresτ C hC f hf) w
  refine ⟨fun σ hσ w => ?_, fun σ hσ w => ?_⟩
  ·
    obtain ⟨d, hdI, rfl⟩ := Subgroup.mem_map.mp hσ
    have hd1 : ∀ x : ResidueField ↥A, d • x = RingHom.id (ResidueField ↥A) x := by
      intro x
      have h := RingEquiv.congr_fun (MonoidHom.mem_ker.mp hdI) x
      simpa using h
    have key := main d (RingHom.id _) hd1 1 (fun y => by rw [one_smul, coeffMap_id]) w
    rw [one_smul] at key
    exact key
  ·
    obtain ⟨hσD, hfrob⟩ := hσ
    have key := main ⟨σ, hσD⟩ (frobenius (ResidueField ↥A) p)
      (fun x => (hfrob x).trans (frobenius_def p x).symm)
      (qExpArithFrobC p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))
      (coe_qExpArithFrobC_smul p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)) w
    rw [qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul]
    exact key

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_sp_smul_eq_of_mem_inertiaSubgroupIn_and_sp_smul_eq_qExpFrobeniusPlaceModL_of_isFrobeniusAt (solution)
