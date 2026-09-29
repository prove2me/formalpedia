-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/12f84032-e223-5cf1-b52c-c9be37103bf7

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_zero RegularProlongation Annulus"
p2m_open "AlgebraicCurve"

theorem map_units_zpow_aux {M N : Type*} [Monoid M] [DivisionMonoid N] (φ : M →* N) (u : Mˣ) (n : ℤ) :
    φ ((u ^ n : Mˣ) : M) = (φ (u : M)) ^ n := by
  rw [← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField ord ord_zero ord_mul ord_inv ord_coe_unit ord_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring residue_algebraMap IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt"
p2m_open "AlgebraicCurve.Place"

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.evalAt_eq_zero_of_not_isUnit' {f : F} (hf : f ∈ v.toValuationSubring)
    (h : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : v.evalAt f = 0 := by
  rw [v.evalAt_of_mem hf]
  have hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal _).mpr h
  have h0 : residue v.toValuationSubring ⟨f, hf⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hm
  rw [h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_eq_zero_of_not_isUnit'"
private theorem _root_.AlgebraicCurve.Place.isUnit_of_evalAt_ne_zero' {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra hu
  exact h (v.evalAt_eq_zero_of_not_isUnit' hf hu)

p2m_export "AlgebraicCurve.Place" "isUnit_of_evalAt_ne_zero'"
private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_isUnit' {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : v.ord f = 0 := by
  obtain ⟨u, hu⟩ := hu
  have h := v.ord_coe_unit u
  rwa [hu] at h

p2m_export "AlgebraicCurve.Place" "ord_eq_zero_of_isUnit'"
private theorem _root_.AlgebraicCurve.Place.exists_isUnit_of_ord_eq_zero' {f : F} (hf0 : f ≠ 0) (h : v.ord f = 0) :
    ∃ hf : f ∈ v.toValuationSubring, IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  rw [h, zpow_zero, mul_one] at hu
  have hmem : f ∈ v.toValuationSubring := by rw [hu]; exact (u : v.toValuationSubring).2
  refine ⟨hmem, ?_⟩
  have he : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
  rw [he]
  exact u.isUnit

p2m_export "AlgebraicCurve.Place" "exists_isUnit_of_ord_eq_zero'"
private theorem _root_.AlgebraicCurve.Place.ord_algebraMap' (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · refine v.ord_eq_zero_of_isUnit' (v.algebraMap_mem' a) ⟨⟨⟨_, v.algebraMap_mem' a⟩, ⟨_, v.algebraMap_mem' a⁻¹⟩,
      Subtype.ext (by simp [ha]), Subtype.ext (by simp [ha])⟩, rfl⟩

p2m_export "AlgebraicCurve.Place" "ord_algebraMap'"

private noncomputable def _root_.AlgebraicCurve.Place.evalRingHom' (hv : v.IsRational) : v.toValuationSubring →+* K :=
  (RingEquiv.ofBijective (algebraMap K v.ResidueField) ⟨v.algebraMap_residueField_injective, hv⟩).symm.toRingHom.comp
    (residue v.toValuationSubring)

p2m_export "AlgebraicCurve.Place" "evalRingHom'"
private theorem _root_.AlgebraicCurve.Place.evalAt_eq_evalRingHom' (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.evalRingHom' hv ⟨f, hf⟩ := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hf]
  simp only [evalRingHom', RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply]
  rw [← RingEquiv.ofBijective_apply (algebraMap K v.ResidueField) ⟨v.algebraMap_residueField_injective, hv⟩,
    RingEquiv.apply_symm_apply]

p2m_export "AlgebraicCurve.Place" "evalAt_eq_evalRingHom'"
private theorem _root_.AlgebraicCurve.Place.evalAt_mul' (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  rw [v.evalAt_eq_evalRingHom' hv (mul_mem hf hg), v.evalAt_eq_evalRingHom' hv hf, v.evalAt_eq_evalRingHom' hv hg,
    ← map_mul]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_mul'"
private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap' (hv : v.IsRational) (a : K) : v.evalAt (algebraMap K F a) = a := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.algebraMap_mem' a), IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_algebraMap'"
private theorem _root_.AlgebraicCurve.Place.zpow_mem_and_evalAt_zpow' (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℤ) :
    ∃ _ : f ^ n ∈ v.toValuationSubring, v.evalAt (f ^ n) = (v.evalAt f) ^ n := by
  obtain ⟨u, hu⟩ := hu
  have hval : ((u : v.toValuationSubring) : F) = f := by rw [hu]
  have hz : (((u ^ n : v.toValuationSubringˣ) : v.toValuationSubring) : F) = f ^ n := by
    rw [← hval]
    exact map_units_zpow_aux (v.toValuationSubring.subtype.toMonoidHom) u n
  have hmem : f ^ n ∈ v.toValuationSubring := by rw [← hz]; exact ((u ^ n : v.toValuationSubringˣ) : v.toValuationSubring).2
  refine ⟨hmem, ?_⟩
  rw [v.evalAt_eq_evalRingHom' hv hmem, v.evalAt_eq_evalRingHom' hv hf]
  have he : (⟨f ^ n, hmem⟩ : v.toValuationSubring) = ((u ^ n : v.toValuationSubringˣ) : v.toValuationSubring) :=
    Subtype.ext hz.symm
  rw [he, ← hu]
  exact map_units_zpow_aux (v.evalRingHom' hv).toMonoidHom u n

p2m_export "AlgebraicCurve.Place" "zpow_mem_and_evalAt_zpow'"
end Place

namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero integers residue_algebraMap algebraMap_mem_iff residue"
p2m_open "AlgebraicCurve.RegularProlongation"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem endSlope_of_unitRead (R : RegularProlongation A F Fbar) (x : Place (ResidueField A) Fbar)
    (dom : Set (Place L F)) (w : F)
    (hdom : ∀ P ∈ dom, P.IsRational ∧ w ∈ P.toValuationSubring ∧ P.evalAt w ≠ 0)
    (hup : ∀ f : F, f ≠ 0 → (∀ P ∈ dom, P.ord f = 0) →
      ∃ (m : ℤ) (c : L), c ≠ 0 ∧ ∀ P ∈ dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt w) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A))
    (hw : ∃ h : w ∈ R.integers, x.ord (R.residue ⟨w, h⟩) = 1)
    (hu : ∀ g : F, g ≠ 0 → (∀ P ∈ dom, P.ord g = 0) → (∀ P ∈ dom, ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : A)) →
      ∃ hg : g ∈ R.integers, R.residue ⟨g, hg⟩ ≠ 0 ∧ x.ord (R.residue ⟨g, hg⟩) = 0)
    (f : F) (hf : f ∈ R.integers) (hres : R.residue ⟨f, hf⟩ ≠ 0) (hord : ∀ P ∈ dom, P.ord f = 0)
    (P : Place L F) (hP : P ∈ dom) :
    ∃ h : P.evalAt f * (P.evalAt w) ^ (-(x.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  obtain ⟨hwR, hw1⟩ := hw
  have hreswne : R.residue ⟨w, hwR⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hw1; exact zero_ne_one hw1
  have hwunit : IsUnit (⟨w, hwR⟩ : R.integers) := R.isUnit_of_residue_ne_zero hreswne
  have hw0 : w ≠ 0 := by
    intro h; apply hreswne
    have : (⟨w, hwR⟩ : R.integers) = 0 := Subtype.ext h
    rw [this, map_zero]
  have hf0 : f ≠ 0 := by
    intro h; apply hres
    have : (⟨f, hf⟩ : R.integers) = 0 := Subtype.ext h
    rw [this, map_zero]
  obtain ⟨m, c, hc0, hmc⟩ := hup f hf0 hord
  have hcF : algebraMap L F c ≠ 0 := (map_ne_zero _).mpr hc0

  obtain ⟨g, hg_def⟩ : ∃ g : F, g = f * (algebraMap L F c)⁻¹ * w ^ (-m) := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := by
    rw [hg_def]; exact mul_ne_zero (mul_ne_zero hf0 (inv_ne_zero hcF)) (zpow_ne_zero _ hw0)
  have hg_ord : ∀ Q ∈ dom, Q.ord g = 0 := by
    intro Q hQ
    obtain ⟨hQr, hwQ, hwQ0⟩ := hdom Q hQ
    have hwQu := Q.isUnit_of_evalAt_ne_zero' hwQ hwQ0
    rw [hg_def, Q.ord_mul (mul_ne_zero hf0 (inv_ne_zero hcF)) (zpow_ne_zero _ hw0),
      Q.ord_mul hf0 (inv_ne_zero hcF), hord Q hQ, Q.ord_inv, Q.ord_algebraMap', Q.ord_zpow,
      Q.ord_eq_zero_of_isUnit' hwQ hwQu]
    simp
  have hg_eval : ∀ Q ∈ dom, Q.evalAt g = Q.evalAt f * c⁻¹ * (Q.evalAt w) ^ (-m) := by
    intro Q hQ
    obtain ⟨hQr, hwQ, hwQ0⟩ := hdom Q hQ
    have hwQu := Q.isUnit_of_evalAt_ne_zero' hwQ hwQ0
    obtain ⟨hfQ, -⟩ := Q.exists_isUnit_of_ord_eq_zero' hf0 (hord Q hQ)
    obtain ⟨hwm, hwev⟩ := Q.zpow_mem_and_evalAt_zpow' hQr hwQ hwQu (-m)
    have hcQ : (algebraMap L F c)⁻¹ ∈ Q.toValuationSubring := by
      rw [← map_inv₀]; exact Q.algebraMap_mem' _
    rw [hg_def, Q.evalAt_mul' hQr (mul_mem hfQ hcQ) hwm, Q.evalAt_mul' hQr hfQ hcQ, hwev, ← map_inv₀,
      Q.evalAt_algebraMap' hQr]
  have hg_val : ∀ Q ∈ dom, ∃ h : Q.evalAt g ∈ A, IsUnit (⟨_, h⟩ : A) := by
    intro Q hQ
    rw [hg_eval Q hQ]
    exact hmc Q hQ
  obtain ⟨hgR, hgres, hgord⟩ := hu g hg0 hg_ord hg_val

  obtain ⟨wu, hwu⟩ := hwunit
  have hwuF : ((wu : R.integers) : F) = w := by rw [hwu]
  have hwmF : (((wu ^ m : (R.integers)ˣ) : R.integers) : F) = w ^ m := by
    rw [← hwuF]; exact map_units_zpow_aux R.integers.subtype.toMonoidHom wu m
  obtain ⟨q, hq_def⟩ : ∃ q : R.integers, q = ((wu ^ m : (R.integers)ˣ) : R.integers) * ⟨g, hgR⟩ := ⟨_, rfl⟩
  have hqF : (q : F) = w ^ m * g := by rw [hq_def]; simp [hwmF]
  have hzp : R.residue ((wu ^ m : (R.integers)ˣ) : R.integers) = (R.residue (wu : R.integers)) ^ m :=
    map_units_zpow_aux R.residue.toMonoidHom wu m
  have hq_res : R.residue q = (R.residue (wu : R.integers)) ^ m * R.residue ⟨g, hgR⟩ := by
    rw [hq_def, map_mul, hzp]
  have hreswu : R.residue (wu : R.integers) ≠ 0 := by rw [hwu]; exact hreswne
  have hq_res_ne : R.residue q ≠ 0 := by
    rw [hq_res]; exact mul_ne_zero (zpow_ne_zero _ hreswu) hgres
  have hq_ord : x.ord (R.residue q) = m := by
    rw [hq_res, x.ord_mul (zpow_ne_zero _ hreswu) hgres, x.ord_zpow, hwu, hw1, hgord]; ring

  have hfq : f = algebraMap L F c * (q : F) := by
    rw [hqF, hg_def, zpow_neg]
    field_simp

  have hcA : c ∈ A := by
    by_contra hcA
    have hciA : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hci_res : IsLocalRing.residue A ⟨c⁻¹, hciA⟩ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      apply hcA
      obtain ⟨u, hu'⟩ := hunit
      have h1 : ((u : A) : L) = c⁻¹ := by rw [hu']
      have h2 : ((u : A) : L) * (((u⁻¹ : Aˣ) : A) : L) = 1 := by
        rw [← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
      rw [h1] at h2
      have h3 : c = (((u⁻¹ : Aˣ) : A) : L) := (inv_mul_eq_one₀ hc0).mp h2
      rw [h3]
      exact ((u⁻¹ : Aˣ) : A).2

    have hmem : algebraMap L F c⁻¹ ∈ R.integers := (R.algebraMap_mem_iff _).mpr hciA
    have hq' : q = ⟨algebraMap L F c⁻¹, hmem⟩ * ⟨f, hf⟩ := by
      apply Subtype.ext
      show (q : F) = algebraMap L F c⁻¹ * f
      rw [hfq, map_inv₀, ← mul_assoc, inv_mul_cancel₀ hcF, one_mul]
    apply hq_res_ne
    rw [hq', map_mul, R.residue_algebraMap ⟨c⁻¹, hciA⟩, hci_res, map_zero, zero_mul]
  have hcres : IsLocalRing.residue A ⟨c, hcA⟩ ≠ 0 := by
    intro h0
    apply hres
    have hmem : algebraMap L F c ∈ R.integers := (R.algebraMap_mem_iff _).mpr hcA
    have hf' : (⟨f, hf⟩ : R.integers) = ⟨algebraMap L F c, hmem⟩ * q := Subtype.ext hfq
    rw [hf', map_mul, R.residue_algebraMap ⟨c, hcA⟩, h0, map_zero, zero_mul]
  have hcunit : IsUnit (⟨c, hcA⟩ : A) := by
    by_contra hnu
    exact hcres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))

  have hford : x.ord (R.residue ⟨f, hf⟩) = m := by
    have hmem : algebraMap L F c ∈ R.integers := (R.algebraMap_mem_iff _).mpr hcA
    have hf' : (⟨f, hf⟩ : R.integers) = ⟨algebraMap L F c, hmem⟩ * q := Subtype.ext hfq
    rw [hf', map_mul, R.residue_algebraMap ⟨c, hcA⟩,
      x.ord_mul ((map_ne_zero _).mpr hcres) hq_res_ne, x.ord_algebraMap', hq_ord, zero_add]

  rw [hford]
  obtain ⟨h, hunit⟩ := hmc P hP
  have heq : P.evalAt f * P.evalAt w ^ (-m) = c * (P.evalAt f * c⁻¹ * P.evalAt w ^ (-m)) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [heq]; exact mul_mem hcA h
  · have : (⟨P.evalAt f * P.evalAt w ^ (-m), by rw [heq]; exact mul_mem hcA h⟩ : A) = ⟨c, hcA⟩ * ⟨_, h⟩ :=
      Subtype.ext heq
    rw [this]; exact hcunit.mul hunit

end RegularProlongation

end AlgebraicCurve

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (s : ↥SS) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))

    (hz₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1)
    (hz₁ : ∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1)

    (hu₂ : ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → (∀ P ∈ An.dom, ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) →
      ∃ hg : g ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 ∧ s.1.2.ord (Rpd.R₂.residue ⟨g, hg⟩) = 0)
    (hu₁ : ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → (∀ P ∈ An.dom, ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) →
      ∃ hg : g ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 ∧ s.1.1.ord (Rpd.R₁.residue ⟨g, hg⟩) = 0) :
    (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
    (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
            (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by

  have hdom₂ : ∀ P ∈ An.dom, P.IsRational ∧ An.param ∈ P.toValuationSubring ∧ P.evalAt An.param ≠ 0 := by
    intro P hP
    obtain ⟨hr, hmem, -, hne, -⟩ := An.mem_dom P hP
    exact ⟨hr, hmem, hne⟩

  obtain ⟨h₁, hz1ord⟩ := hz₁
  have hw0 : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ≠ 0 := by
    intro h0
    have : Rpd.R₁.residue ⟨_, h₁⟩ = 0 := by
      have he : (⟨_, h₁⟩ : Rpd.R₁.integers) = 0 := Subtype.ext h0
      rw [he, map_zero]
    rw [this, Place.ord_zero] at hz1ord
    exact zero_ne_one hz1ord
  have hmod0 : ((An.modulus : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0; apply hw0; rw [h0, map_zero, zero_mul]
  have hevalw : ∀ P ∈ An.dom,
      (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ P.toValuationSubring) ∧
      P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹) =
        ((An.modulus : ↥A) : AlgebraicClosure ℚ) * (P.evalAt An.param)⁻¹ := by
    intro P hP
    obtain ⟨hr, hmem, hne⟩ := hdom₂ P hP
    have hzu := P.isUnit_of_evalAt_ne_zero' hmem hne
    obtain ⟨hinvmem, hinvev⟩ := P.zpow_mem_and_evalAt_zpow' hr hmem hzu (-1)
    rw [zpow_neg, zpow_one] at hinvmem hinvev
    refine ⟨mul_mem (P.algebraMap_mem' _) hinvmem, ?_⟩
    rw [P.evalAt_mul' hr (P.algebraMap_mem' _) hinvmem, P.evalAt_algebraMap' hr, hinvev, zpow_neg, zpow_one]
  have hdom₁ : ∀ P ∈ An.dom, P.IsRational ∧
      (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ P.toValuationSubring) ∧
      P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹) ≠ 0 := by
    intro P hP
    obtain ⟨hr, hmem, hne⟩ := hdom₂ P hP
    obtain ⟨hwmem, hwev⟩ := hevalw P hP
    refine ⟨hr, hwmem, ?_⟩
    rw [hwev]
    exact mul_ne_zero hmod0 (inv_ne_zero hne)

  have hup₁ : ∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧ ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * c⁻¹ * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^ (-m) ∈ A,
          IsUnit (⟨_, h⟩ : ↥A) := by
    intro f hf0 hord
    obtain ⟨m, c, hc0, hmc⟩ := An.unit_principle f hf0 hord
    refine ⟨-m, c * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ m, mul_ne_zero hc0 (zpow_ne_zero _ hmod0), fun P hP => ?_⟩
    obtain ⟨-, -, hne⟩ := hdom₂ P hP
    obtain ⟨-, hwev⟩ := hevalw P hP
    have heq : P.evalAt f * (c * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ m)⁻¹ *
        (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^ (-(-m)) =
        P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) := by
      rw [hwev, neg_neg, mul_zpow, inv_zpow', mul_inv]
      field_simp
    rw [heq]
    exact hmc P hP
  obtain ⟨h₂, hz2ord⟩ := hz₂
  refine ⟨⟨h₂, hz2ord, fun f hf hres hord P hP => ?_⟩, ⟨h₁, hz1ord, fun f hf hres hord P hP => ?_⟩⟩
  · exact AlgebraicCurve.RegularProlongation.endSlope_of_unitRead Rpd.R₂ s.1.2 An.dom An.param hdom₂
      (fun f hf0 hord' => An.unit_principle f hf0 hord') ⟨h₂, hz2ord⟩ hu₂ f hf hres hord P hP
  · exact AlgebraicCurve.RegularProlongation.endSlope_of_unitRead Rpd.R₁ s.1.1 An.dom _ hdom₁ hup₁ ⟨h₁, hz1ord⟩ hu₁ f hf hres hord P hP

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers (solution)
