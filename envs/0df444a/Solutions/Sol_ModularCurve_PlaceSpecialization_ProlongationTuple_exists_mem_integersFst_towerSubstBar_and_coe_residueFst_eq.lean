-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ef778b8d-35e1-5bee-92c5-aa01746eb8e8

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace SubstGaussAux

local notation "Qb" => AlgebraicClosure ℚ

section Pack

variable (A : ValuationSubring Qb)

def packA (x : LaurentSeries Qb) (hx : ∀ n : ℤ, x.coeff n ∈ A) : LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

@[scoped simp] theorem packA_coeff (x : LaurentSeries Qb) (hx : ∀ n : ℤ, x.coeff n ∈ A) (n : ℤ) :
    ((packA A x hx).coeff n : Qb) = x.coeff n := rfl

theorem coeffMap_subtype_packA (x : LaurentSeries Qb) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    coeffMap A.subtype (packA A x hx) = x := by
  ext n; rfl

theorem forall_coeff_qExpand_mem (ℓ : ℕ) [NeZero ℓ] {x : LaurentSeries Qb} (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    ∀ n : ℤ, (qExpand Qb ℓ x).coeff n ∈ A := by
  intro n
  by_cases hd : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [qExpand_coeff_mul]; exact hx m
  · rw [qExpand_coeff_of_not_dvd ℓ _ hd]; exact zero_mem _

theorem coeffMap_packA_qExpand {k : Type*} [CommRing k] (red : A →+* k) (ℓ : ℕ) [NeZero ℓ]
    (x : LaurentSeries Qb) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    coeffMap red (packA A (qExpand Qb ℓ x) (forall_coeff_qExpand_mem A ℓ hx))
      = qExpand k ℓ (coeffMap red (packA A x hx)) := by
  have hpack : packA A (qExpand Qb ℓ x) (forall_coeff_qExpand_mem A ℓ hx) = qExpand A ℓ (packA A x hx) := by
    have hinj : Function.Injective (coeffMap A.subtype : LaurentSeries A →+* LaurentSeries Qb) := by
      intro a b h
      ext n
      have := congrArg (fun z : LaurentSeries Qb => z.coeff n) h
      simpa [coeffMap_coeff] using this
    apply hinj
    rw [coeffMap_subtype_packA, coeffSemilinearAut.coeffMap_qExpand, coeffMap_subtype_packA]
  rw [hpack, coeffSemilinearAut.coeffMap_qExpand]

end Pack

section ModRing

variable (A : ValuationSubring Qb) (M : ℕ) [NeZero M]

theorem jqModC_mem_bar : jqModC Qb ∈ modularFunctionFieldBar M := by
  have h1 : jqModC Qb = coeffEmb Qb jq := by
    rw [← jqModC_rat, coeffEmb, coeffSemilinearAut.coeffMap_jqModC]
  rw [h1]
  exact coeffEmb_mem_laurentBaseChange Qb (modularFunctionField_le_full M (jq_mem M))

theorem jqNModC_mem_bar : jqNModC Qb M ∈ modularFunctionFieldBar M := by
  have h1 : jqNModC Qb M = coeffEmb Qb (qExpand ℚ M jq) := by
    rw [jqNModC, ← jqModC_rat, coeffEmb, coeffSemilinearAut.coeffMap_qExpand,
      coeffSemilinearAut.coeffMap_jqModC]
  rw [h1]
  exact coeffEmb_mem_laurentBaseChange Qb (jqd_mem_full M (dvd_refl M))

theorem modularRing_le_bar :
    CharPReduction.modularRing M A.toSubring ≤ (modularFunctionFieldBar M).toSubalgebra.toSubring := by
  rw [CharPReduction.modularRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar M).algebraMap_mem (a : Qb)
  · exact jqModC_mem_bar M
  · exact jqNModC_mem_bar M

theorem mem_bar_of_mem_modularRing {x : LaurentSeries Qb} (hx : x ∈ CharPReduction.modularRing M A.toSubring) :
    x ∈ modularFunctionFieldBar M :=
  modularRing_le_bar A M hx

theorem forall_coeff_mem_of_mem_modularRing {x : LaurentSeries Qb}
    (hx : x ∈ CharPReduction.modularRing M A.toSubring) : ∀ n : ℤ, x.coeff n ∈ A :=
  fun n => CharPReduction.modularRing_le_integralCoeffs M A.toSubring hx n

end ModRing

section Residues

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral Qb N q} {hβ : HeckeBetaBarIntegral Qb N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem redBar_comp_residue : R.redBar.comp (IsLocalRing.residue A) = red :=
  RingHom.ext R.redBar_residue

theorem exists_mem_integersFst_coe_residue₁_eq (x : LaurentSeries Qb) (hx : ∀ n : ℤ, x.coeff n ∈ A)
    (hxF : x ∈ modularFunctionFieldBar (N * q)) :
    ∃ h1 : (⟨x, hxF⟩ : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers,
      ((R.residue₁ ⟨_, h1⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
        = coeffMap red (packA A x hx) := by
  have e : coeffMap A.subtype (packA A x hx) = x := coeffMap_subtype_packA A x hx
  have hyF : coeffMap A.subtype (packA A x hx) ∈ modularFunctionFieldBar (N * q) := by rw [e]; exact hxF
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (packA A x hx) hyF
  have hel : (⟨coeffMap A.subtype (packA A x hx), hyF⟩ : ↥(modularFunctionFieldBar (N * q))) = ⟨x, hxF⟩ :=
    Subtype.ext e
  have h1 : (⟨x, hxF⟩ : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers := by rw [← hel]; exact h
  refine ⟨h1, ?_⟩
  have h2 : (⟨⟨x, hxF⟩, h1⟩ : ↥R.R₁.integers) = ⟨⟨coeffMap A.subtype (packA A x hx), hyF⟩, h⟩ :=
    Subtype.ext hel.symm
  rw [residue₁_apply, R.ι_coe, h2, hres, coeffMap_coeffMap, redBar_comp_residue]

theorem residue_ne_zero_of_residue₁_ne_zero {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ R.R₁.integers)
    (h : R.residue₁ ⟨f, h₁⟩ ≠ 0) : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := by
  intro h0
  apply h
  rw [residue₁_apply, h0, map_zero]

theorem inv_mem_of_isUnit {L : Type*} [Field L] {S : ValuationSubring L} {f : L} (hf : f ∈ S)
    (hu : IsUnit (⟨f, hf⟩ : S)) : f⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : L) = f := by rw [hu]
  have h1 : f * (((u⁻¹ : Sˣ) : S) : L) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      OneMemClass.coe_one]
  have h2 : (((u⁻¹ : Sˣ) : S) : L) = f⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [← h2]
  exact SetLike.coe_mem _

end Residues

end SubstGaussAux
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq.SubstGaussAux"

open SubstGaussAux in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (ℓ : ℕ) [NeZero ℓ]
    {dataᵣ : ModularPolynomialData q} {hKrᵣ : KroneckerCongruence q dataᵣ}
    {hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {Pᵣ : PlaceSpecialization A q (N * ℓ) dataᵣ hKrᵣ k red hαᵣ hβᵣ} (Rᵣ : ProlongationTuple Pᵣ)
    (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) :
    ∃ h' : towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
        (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q) f ∈ Rᵣ.R₁.integers,
      ((Rᵣ.residue₁ ⟨_, h'⟩ : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k)
        = qExpand k ℓ ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) := by

  obtain ⟨r, s, hs, hfs⟩ := (R.mem_integersFst_iff f).mp h
  have hrF : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (N * q) := mem_bar_of_mem_modularRing A _ r.2
  have hsF : (s : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (N * q) := mem_bar_of_mem_modularRing A _ s.2
  have hrA := forall_coeff_mem_of_mem_modularRing A (N * q) r.2
  have hsA := forall_coeff_mem_of_mem_modularRing A (N * q) s.2
  set ι := towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
    (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q) with hιdef
  set rF : ↥(modularFunctionFieldBar (N * q)) := ⟨r, hrF⟩ with hrFdef
  set sF : ↥(modularFunctionFieldBar (N * q)) := ⟨s, hsF⟩ with hsFdef
  have hfs' : f * sF = rF := Subtype.ext hfs

  obtain ⟨hr1, hres_r⟩ := exists_mem_integersFst_coe_residue₁_eq R (r : LaurentSeries (AlgebraicClosure ℚ)) hrA hrF
  obtain ⟨hs1, hres_s⟩ := exists_mem_integersFst_coe_residue₁_eq R (s : LaurentSeries (AlgebraicClosure ℚ)) hsA hsF

  have hreds : coeffMap red (packA A (s : LaurentSeries (AlgebraicClosure ℚ)) hsA) ≠ 0 := by
    have hs' := (CharPReduction.notMem_redKer_iff A.toSubring red _ _).mp hs
    intro h0
    apply hs'
    rw [CharPReduction.redRes_apply]
    ext n
    rw [CharPReduction.coeffRed_coeff, HahnSeries.coeff_zero]
    have := congrArg (fun z : LaurentSeries k => z.coeff n) h0
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
    exact this
  have hress_ne : (R.residue₁ ⟨sF, hs1⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    intro h0; apply hreds
    rw [← hres_s, h0]; rfl

  have hres_f : ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
      = coeffMap red (packA A (r : LaurentSeries (AlgebraicClosure ℚ)) hrA) / coeffMap red (packA A (s : LaurentSeries (AlgebraicClosure ℚ)) hsA) := by
    have hmul : (⟨f, h⟩ : ↥R.R₁.integers) * ⟨sF, hs1⟩ = ⟨rF, hr1⟩ := Subtype.ext hfs'
    have h1 : R.residue₁ ⟨f, h⟩ * R.residue₁ ⟨sF, hs1⟩ = R.residue₁ ⟨rF, hr1⟩ := by rw [← map_mul, hmul]
    have h2 := congrArg (fun z : ↥(modularFunctionFieldC k N) => (z : LaurentSeries k)) h1
    simp only [MulMemClass.coe_mul] at h2
    rw [hres_r, hres_s] at h2
    rw [eq_div_iff hreds, h2]

  have hιr : (ι rF : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) ℓ (r : LaurentSeries (AlgebraicClosure ℚ)) := rfl
  have hιs : (ι sF : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) ℓ (s : LaurentSeries (AlgebraicClosure ℚ)) := rfl
  obtain ⟨hr1', hres_r'⟩ := exists_mem_integersFst_coe_residue₁_eq Rᵣ (qExpand (AlgebraicClosure ℚ) ℓ (r : LaurentSeries (AlgebraicClosure ℚ)))
    (forall_coeff_qExpand_mem A ℓ hrA) (ι rF).2
  obtain ⟨hs1', hres_s'⟩ := exists_mem_integersFst_coe_residue₁_eq Rᵣ (qExpand (AlgebraicClosure ℚ) ℓ (s : LaurentSeries (AlgebraicClosure ℚ)))
    (forall_coeff_qExpand_mem A ℓ hsA) (ι sF).2
  rw [coeffMap_packA_qExpand A red ℓ _ hrA] at hres_r'
  rw [coeffMap_packA_qExpand A red ℓ _ hsA] at hres_s'
  have her : (⟨qExpand (AlgebraicClosure ℚ) ℓ (r : LaurentSeries (AlgebraicClosure ℚ)), (ι rF).2⟩ : ↥(modularFunctionFieldBar (N * ℓ * q))) = ι rF :=
    Subtype.ext rfl
  have hes : (⟨qExpand (AlgebraicClosure ℚ) ℓ (s : LaurentSeries (AlgebraicClosure ℚ)), (ι sF).2⟩ : ↥(modularFunctionFieldBar (N * ℓ * q))) = ι sF :=
    Subtype.ext rfl
  have hr1'' : ι rF ∈ Rᵣ.R₁.integers := by rw [← her]; exact hr1'
  have hs1'' : ι sF ∈ Rᵣ.R₁.integers := by rw [← hes]; exact hs1'
  have hres_r'' : ((Rᵣ.residue₁ ⟨ι rF, hr1''⟩ : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k)
      = qExpand k ℓ (coeffMap red (packA A (r : LaurentSeries (AlgebraicClosure ℚ)) hrA)) := by
    have e1 : (⟨ι rF, hr1''⟩ : ↥Rᵣ.R₁.integers)
        = ⟨⟨qExpand (AlgebraicClosure ℚ) ℓ (r : LaurentSeries (AlgebraicClosure ℚ)), (ι rF).2⟩, hr1'⟩ :=
      Subtype.ext her.symm
    rw [e1]; exact hres_r'
  have hres_s'' : ((Rᵣ.residue₁ ⟨ι sF, hs1''⟩ : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k)
      = qExpand k ℓ (coeffMap red (packA A (s : LaurentSeries (AlgebraicClosure ℚ)) hsA)) := by
    have e1 : (⟨ι sF, hs1''⟩ : ↥Rᵣ.R₁.integers)
        = ⟨⟨qExpand (AlgebraicClosure ℚ) ℓ (s : LaurentSeries (AlgebraicClosure ℚ)), (ι sF).2⟩, hs1'⟩ :=
      Subtype.ext hes.symm
    rw [e1]; exact hres_s'

  have hqinj : Function.Injective (qExpand k ℓ) := (qExpand k ℓ).injective
  have hreds' : qExpand k ℓ (coeffMap red (packA A (s : LaurentSeries (AlgebraicClosure ℚ)) hsA)) ≠ 0 :=
    (map_ne_zero_iff _ hqinj).mpr hreds
  have hress'_ne : (Rᵣ.residue₁ ⟨ι sF, hs1''⟩ : ↥(modularFunctionFieldC k (N * ℓ))) ≠ 0 := by
    intro h0; apply hreds'
    rw [← hres_s'', h0]; rfl
  have hsu : IsUnit (⟨ι sF, hs1''⟩ : ↥Rᵣ.R₁.integers) :=
    Rᵣ.R₁.isUnit_of_residue_ne_zero (residue_ne_zero_of_residue₁_ne_zero Rᵣ hs1'' hress'_ne)
  have hsinv : (ι sF)⁻¹ ∈ Rᵣ.R₁.integers := inv_mem_of_isUnit hs1'' hsu
  have hs0 : ι sF ≠ 0 := by
    intro h0; apply hress'_ne
    have : (⟨ι sF, hs1''⟩ : ↥Rᵣ.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hιf : ι f = ι rF * (ι sF)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, hfs']
  have h' : ι f ∈ Rᵣ.R₁.integers := by rw [hιf]; exact mul_mem hr1'' hsinv
  refine ⟨h', ?_⟩
  have hmul : (⟨ι f, h'⟩ : ↥Rᵣ.R₁.integers) * ⟨ι sF, hs1''⟩ = ⟨ι rF, hr1''⟩ :=
    Subtype.ext (by rw [MulMemClass.coe_mul]; exact (eq_mul_inv_iff_mul_eq₀ hs0).mp hιf)
  have h1 : Rᵣ.residue₁ ⟨ι f, h'⟩ * Rᵣ.residue₁ ⟨ι sF, hs1''⟩ = Rᵣ.residue₁ ⟨ι rF, hr1''⟩ := by
    rw [← map_mul, hmul]
  have h2 := congrArg (fun z : ↥(modularFunctionFieldC k (N * ℓ)) => (z : LaurentSeries k)) h1
  simp only [MulMemClass.coe_mul] at h2
  rw [hres_r'', hres_s''] at h2
  rw [hres_f, map_div₀, eq_div_iff hreds', h2]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq (solution)
