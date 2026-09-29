-- Prove2me | solution 1 for ModularCurve.exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/950e5c5a-d72c-5c6d-867f-340136d7611b

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective

set_option autoImplicit false

open ModularCurve

namespace E148I2

def inclA {k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)} (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (A₁ : ValuationSubring ↥K₁)
    (h : ∀ a : ↥A₁, ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A) : ↥A₁ →+* ↥A where
  toFun a := ⟨((a : ↥K₁) : AlgebraicClosure ℚ), h a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem isLocalHom_inclA {k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)} (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (A₁ : ValuationSubring ↥K₁)
    (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    IsLocalHom (inclA K₁ A A₁ (fun a => (hA₁ a).mp a.2)) := by
  constructor
  intro a ha
  have hτ : ∀ a, ((inclA K₁ A A₁ (fun a => (hA₁ a).mp a.2) a : ↥A) : AlgebraicClosure ℚ) =
    ((a : ↥K₁) : AlgebraicClosure ℚ) := fun _ => rfl
  rw [ValuationSubring.valuation_eq_one_iff] at ha ⊢
  by_contra hne
  have hlt : A₁.valuation (a : ↥K₁) < 1 := lt_of_le_of_ne (A₁.valuation_le_one a) hne
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hlt
  have ha' : ¬ (A.valuation ((inclA K₁ A A₁ (fun a => (hA₁ a).mp a.2) a : ↥A) : AlgebraicClosure ℚ) < 1) := by
    rw [ha]; exact lt_irrefl 1
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, hτ] at ha'
  push Not at ha'
  rcases hlt with h0 | hinv
  · exact ha'.1 (by rw [h0]; simp)
  · exact hinv ((hA₁ _).mpr (by simpa using ha'.2))

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g) :
    Function.Injective (ModularCurve.coeffMap g) := by
  intro x y h
  ext n
  apply hg
  have := congrArg (fun z => HahnSeries.coeff z n) h
  simpa [ModularCurve.coeffMap_coeff] using this

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map f) := by
  ext k
  rw [coeffMap_coeff]
  change f (((x : PowerSeries R) : LaurentSeries R).coeff k) = ((x.map f : PowerSeries S) : LaurentSeries S).coeff k
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · exact (PowerSeries.coeff_map _ _ _).symm

theorem coeffMap_intSeriesC {K K' : Type*} [Field K] [Field K'] (ρ : K →+* K') (p : PowerSeries ℤ) :
    coeffMap ρ (intSeriesC K p) = intSeriesC K' p := by
  unfold intSeriesC
  rw [coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

end E148I2

open E148I2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)

    (hκ₁ : Function.Surjective
      (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ (a : ↥K₁)).mp a.2⟩))
    (K : IntermediateField ↥K₁ (LaurentSeries ↥K₁))
    (hK : K = ModularCurve.laurentBaseChange ↥K₁ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))

    (O : ValuationSubring ↥E)
    (hO : ∀ f : ↥E, f ∈ O ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (φ : ↥K →+* ↥E)
    (hφ : ∀ f : ↥K, ((φ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁)) :
    ∀ f : ↥E, f ∈ O → ∃ w : ↥K, φ w ∈ O ∧ (f - φ w : ↥E) ∈ O.nonunits := by
  classical
  intro f hf
  subst hK hE

  obtain ⟨R, hRint, -, hRres⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq (AlgebraicClosure ℚ) A Γ hT
  obtain ⟨R₁, hR₁int, -, hR₁res⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq ↥K₁ A₁ Γ hT
  have hOR : ∀ g, g ∈ O ↔ g ∈ R.integers := fun g => (hO g).trans (hRint g).symm

  let τ : ↥A₁ →+* ↥A := inclA K₁ A A₁ (fun a => (hA₁ a).mp a.2)
  haveI : IsLocalHom τ := isLocalHom_inclA K₁ A A₁ hA₁
  let ρ : IsLocalRing.ResidueField ↥A₁ →+* IsLocalRing.ResidueField ↥A := IsLocalRing.ResidueField.map τ
  have hρres : ∀ a, ρ (IsLocalRing.residue ↥A₁ a) = IsLocalRing.residue ↥A (τ a) := fun a => rfl
  have hρsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨a, ha⟩ := hκ₁ c
    exact ⟨IsLocalRing.residue ↥A₁ a, ha⟩
  have hρτ : (IsLocalRing.residue ↥A).comp τ = ρ.comp (IsLocalRing.residue ↥A₁) := RingHom.ext fun _ => rfl
  have hAτ : A.subtype.comp τ = (algebraMap ↥K₁ (AlgebraicClosure ℚ)).comp A₁.subtype := RingHom.ext fun _ => rfl

  have himg : ∀ g : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) Γ),
      ∃ y : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A₁) Γ),
        coeffMap ρ (y : LaurentSeries (IsLocalRing.ResidueField ↥A₁)) = (g : LaurentSeries (IsLocalRing.ResidueField ↥A)) := by
    let Timg : IntermediateField (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) :=
      ((qExpFunctionFieldC (IsLocalRing.ResidueField ↥A₁) Γ).toSubfield.map (coeffMap ρ)).toIntermediateField (by
        intro c
        obtain ⟨c₁, rfl⟩ := hρsurj c
        refine ⟨algebraMap _ _ c₁, (qExpFunctionFieldC (IsLocalRing.ResidueField ↥A₁) Γ).algebraMap_mem c₁, ?_⟩
        rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single]
        exact coeffMap_single ρ 0 c₁)
    have hle : qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) Γ ≤ Timg := by
      change IntermediateField.adjoin _ _ ≤ Timg
      rw [IntermediateField.adjoin_le_iff]
      rintro x ⟨k, fm, gm, pf, pg, hpf, hpg, hg0, rfl⟩
      have hg0' : intSeriesC (IsLocalRing.ResidueField ↥A₁) pg ≠ 0 := by
        intro h; apply hg0; rw [← coeffMap_intSeriesC ρ pg, h, map_zero]
      refine ⟨intSeriesC (IsLocalRing.ResidueField ↥A₁) pf / intSeriesC (IsLocalRing.ResidueField ↥A₁) pg,
        div_mem_qExpFunctionFieldC fm gm hpf hpg hg0', ?_⟩
      rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
    intro g
    obtain ⟨y, hy, hyg⟩ := hle g.2
    exact ⟨⟨y, hy⟩, hyg⟩

  have hfR : f ∈ R.integers := (hOR f).mp hf
  obtain ⟨y, hy⟩ := himg (R.residue ⟨f, hfR⟩)
  obtain ⟨⟨w, hw⟩, hw'⟩ := R₁.residue_surjective y

  obtain ⟨x₁, y₁, hy₁, hpres⟩ := (hR₁int w).mp hw
  have hpresφ : ((φ w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) :
      LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype (coeffMap τ y₁) = coeffMap A.subtype (coeffMap τ x₁) := by
    rw [hφ, coeffMap_coeffMap, coeffMap_coeffMap, hAτ, ← coeffMap_coeffMap, ← coeffMap_coeffMap, ← map_mul, hpres]
  have aux : ∀ z : LaurentSeries ↥A₁, coeffMap (IsLocalRing.residue ↥A) (coeffMap τ z) =
      coeffMap ρ (coeffMap (IsLocalRing.residue ↥A₁) z) := fun z => by
    rw [coeffMap_coeffMap, coeffMap_coeffMap, hρτ]
  have hne : coeffMap ρ (coeffMap (IsLocalRing.residue ↥A₁) y₁) ≠ 0 :=
    fun h => hy₁ (coeffMap_injective ρ ρ.injective (by rw [h, map_zero]))
  have hy₁' : coeffMap (IsLocalRing.residue ↥A) (coeffMap τ y₁) ≠ 0 := by
    rw [aux]; exact hne
  have hφwO : φ w ∈ O := (hO _).mpr ⟨coeffMap τ x₁, coeffMap τ y₁, hy₁', hpresφ⟩
  have hφwR : φ w ∈ R.integers := (hOR _).mp hφwO

  have hres_eq : R.residue ⟨φ w, hφwR⟩ = R.residue ⟨f, hfR⟩ := by
    apply Subtype.ext
    have h1 := hRres (φ w) hφwR (coeffMap τ x₁) (coeffMap τ y₁) hy₁' hpresφ
    have h2 := hR₁res w hw x₁ y₁ hy₁ hpres
    have h2' := congrArg (coeffMap ρ) h2
    rw [(coeffMap ρ).map_mul] at h2'
    rw [aux, aux] at h1
    have := mul_right_cancel₀ hne (h1.trans h2'.symm)
    rw [this, hw', hy]

  refine ⟨w, hφwO, ?_⟩
  have hOeq : O = R.integers := SetLike.ext hOR
  rw [hOeq]
  have hmem : (f - φ w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) ∈ R.integers :=
    R.integers.sub_mem hfR hφwR
  have : (⟨f - φ w, hmem⟩ : ↥R.integers) ∈ IsLocalRing.maximalIdeal ↥R.integers := by
    rw [← R.ker_residue, RingHom.mem_ker]
    have : (⟨f - φ w, hmem⟩ : ↥R.integers) = ⟨f, hfR⟩ - ⟨φ w, hφwR⟩ := rfl
    rw [this, map_sub, hres_eq, sub_self]
  exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f - φ w, hmem⟩)).mpr this

end S_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
end P2MW
export P2MW.S_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective (solution)
