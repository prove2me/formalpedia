-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.certificate_of_K5_pde
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:38:48.590056+00:00
-- url     : https://prove2.me/submissions/95098deb-5596-486c-817b-5445f0a709be

import Definitions.Def_DiamondCertificate
import Definitions.Def_HodgeComputerSymmetricSexticResidual
import Definitions.Def_HodgeComputerFormal_Algebra
import Definitions.Def_HodgeComputerSSR_PhysicalField
import Definitions.Def_HodgeComputerSSR_K5Field
import Theorems.Thm_HodgeComputer_Formal_HoldoutCover_piola_divergence
import Theorems.Thm_HodgeComputer_Formal_HoldoutCover_piola_contraction
import Theorems.Thm_HodgeComputer_Formal_ResidueTransport_injective_of_coordinate_derivations
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false

/-! Ambient 6×6 Piola pullback from the reduced 5-variable hypersurface field `K5`
to the physical sextic `F_6 = Q_Y^3 F_5`, closing `HodgeComputer.HasCertificate`
without any normal-change correction. -/

noncomputable section
namespace SymmetricSexticResidual.SymmetricPiola
open SymmetricSexticResidual SymmetricSexticResidual.K5Field
open MvPolynomial HoldoutConstruction
open scoped BigOperators Matrix

instance : CharZero AmbientField :=
  charZero_of_injective_ringHom (f := (algebraMap Poly6 AmbientField).comp MvPolynomial.C)
    ((IsFractionRing.injective Poly6 AmbientField).comp (MvPolynomial.C_injective (Fin 6) ℂ))

instance : CharZero FunctionField := by
  refine charZero_of_injective_ringHom (f := residueMap.comp MvPolynomial.C) ?_
  intro a b hab
  have hsub : residueMap (C (a - b)) = 0 := by
    change residueMap (C a) = residueMap (C b) at hab
    rw [map_sub, map_sub, hab, sub_self]
  rw [residueMap_eq_zero_iff] at hsub
  obtain ⟨q, hq⟩ := hsub
  have hev := congrArg (MvPolynomial.eval ![0, 0, 0, 0, 0, 0]) hq
  have hsex : MvPolynomial.eval ![0, 0, 0, 0, 0, 0] sextic = 0 := by
    simp [sextic, QX, QY]
  simp [hsex] at hev
  exact sub_eq_zero.mp hev

-- 3-variable symmetric polynomial identities (zero 6-variable expansion!)
lemma sum_sixth_eq_sym {R : Type*} [CommRing R] (a b c : R) :
    let e1 := a + b + c
    let e2 := a * b + a * c + b * c
    let e3 := a * b * c
    a ^ 6 + b ^ 6 + c ^ 6 =
      e1 ^ 6 - 6 * e1 ^ 4 * e2 + 9 * e1 ^ 2 * e2 ^ 2 - 2 * e2 ^ 3 +
      6 * e1 ^ 3 * e3 - 12 * e1 * e2 * e3 + 3 * e3 ^ 2 := by
  dsimp only; ring

lemma disc_sq_eq_sym {R : Type*} [CommRing R] (a b c : R) :
    let e1 := a + b + c
    let e2 := a * b + a * c + b * c
    let e3 := a * b * c
    ((a - b) * (a - c) * (b - c)) ^ 2 =
      e1 ^ 2 * e2 ^ 2 - 4 * e2 ^ 3 - 4 * e1 ^ 3 * e3 - 27 * e3 ^ 2 + 18 * e1 * e2 * e3 := by
  dsimp only; ring

-- Nonvanishing of low-degree homogeneous polynomials modulo `sextic`
private lemma not_dvd_sextic_of_hom_lt {p : Poly6} {k : ℕ} (hk : k < 6)
    (hp : p.IsHomogeneous k) (hne : MvPolynomial.eval ![1, 2, 3, 1, 2, 3] p ≠ 0) :
    residueMap p ≠ 0 := by
  rw [ne_eq, residueMap_eq_zero_iff]
  rintro ⟨q, hq⟩
  let v : Fin 6 → ℂ := ![1, 2, 3, 1, 2, 3]
  let ev : Poly6 →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X)
  have hev_hom {m : ℕ} {f : Poly6} (hf : f.IsHomogeneous m) :
      ev f = Polynomial.C (MvPolynomial.eval v f) * Polynomial.X ^ m := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
    have hterm (d : Fin 6 →₀ ℕ) (hd : d ∈ f.support) :
        ev (monomial d (f.coeff d)) =
          Polynomial.C (f.coeff d * d.prod (fun i n => v i ^ n)) * Polynomial.X ^ m := by
      have hdsum : d.sum (fun _ n => n) = m := by
        simpa [Finsupp.weight_apply] using hf (MvPolynomial.mem_support_iff.mp hd)
      dsimp only [ev]
      rw [eval₂Hom_monomial]
      have hprod : (d.prod fun i n => (Polynomial.C (v i) * Polynomial.X) ^ n) =
          Polynomial.C (d.prod fun i n => v i ^ n) * Polynomial.X ^ m := by
        simp_rw [mul_pow, ← map_pow]
        rw [Finsupp.prod_mul, ← map_finsuppProd]
        congr 1
        rw [Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (fun _ _ => pow_zero _),
          Finset.prod_pow_eq_pow_sum]
        have hsum_d : ∑ i : Fin 6, d i = m := by
          simpa [Finsupp.sum_of_support_subset d (Finset.subset_univ _) (fun _ n => n) (fun _ _ => rfl)] using hdsum
        rw [hsum_d]
      rw [hprod, ← mul_assoc, ← map_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
    rfl
  have h1 := congrArg ev hq
  rw [map_mul, hev_hom hp, hev_hom sextic_isHomogeneous] at h1
  have hc := congrArg (fun r : Polynomial ℂ => r.coeff k) h1
  rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl, mul_assoc,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul'] at hc
  have hnot : ¬ 6 ≤ k := by omega
  rw [if_neg hnot, mul_zero] at hc
  exact hne hc

def xNum6 : Poly6 := e3X + e1X ^ 3 - 2 * e1X * QX

lemma residueMap_e1X_ne : residueMap e1X ≠ 0 := by
  refine not_dvd_sextic_of_hom_lt (k := 1) (by decide) ?_ ?_
  · exact ((isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 1)).add (isHomogeneous_X ℂ 2)
  · simp [e1X]; norm_num

lemma residueMap_e1Y_ne : residueMap e1Y ≠ 0 := by
  refine not_dvd_sextic_of_hom_lt (k := 1) (by decide) ?_ ?_
  · exact ((isHomogeneous_X ℂ 3).add (isHomogeneous_X ℂ 4)).add (isHomogeneous_X ℂ 5)
  · simp [e1Y]; norm_num

lemma residueMap_QY_ne : residueMap QY ≠ 0 := by
  refine not_dvd_sextic_of_hom_lt (k := 2) (by decide) QY_isHomogeneous ?_
  simp [QY]; norm_num

lemma residueMap_ΔX_ne : residueMap ΔX ≠ 0 := by
  refine not_dvd_sextic_of_hom_lt (k := 3) (by decide) ?_ ?_
  · exact (((isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ 1)).mul
      ((isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ 2))).mul
      ((isHomogeneous_X ℂ 1).sub (isHomogeneous_X ℂ 2))
  · simp [ΔX]; norm_num

lemma residueMap_ΔY_ne : residueMap ΔY ≠ 0 := by
  refine not_dvd_sextic_of_hom_lt (k := 3) (by decide) ?_ ?_
  · exact (((isHomogeneous_X ℂ 3).sub (isHomogeneous_X ℂ 4)).mul
      ((isHomogeneous_X ℂ 3).sub (isHomogeneous_X ℂ 5))).mul
      ((isHomogeneous_X ℂ 4).sub (isHomogeneous_X ℂ 5))
  · simp [ΔY]; norm_num

lemma residueMap_xNum6_ne : residueMap xNum6 ≠ 0 := by
  refine not_dvd_sextic_of_hom_lt (k := 3) (by decide) ?_ ?_
  · have he1 : e1X.IsHomogeneous 1 :=
      ((isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 1)).add (isHomogeneous_X ℂ 2)
    have he3 : e3X.IsHomogeneous 3 :=
      ((isHomogeneous_X ℂ 0).mul (isHomogeneous_X ℂ 1)).mul (isHomogeneous_X ℂ 2)
    have h2 : (2 * e1X * QX).IsHomogeneous 3 := by
      have hc : (2 : Poly6) = MvPolynomial.C 2 := rfl
      rw [hc]
      simpa using ((isHomogeneous_C (Fin 6) (2 : ℂ)).mul he1).mul QX_isHomogeneous
    exact (he3.add (by simpa using he1.pow 3)).sub h2
  · simp [xNum6, e3X, e1X, QX]; norm_num

-- Ambient field and legal-denominator subring (localization at (sextic))
def toAmb : Poly6 →+* AmbientField := algebraMap Poly6 AmbientField

lemma toAmb_ne_of_residue_ne {p : Poly6} (hp : residueMap p ≠ 0) : toAmb p ≠ 0 := by
  intro h
  have hp0 : p = 0 := IsFractionRing.injective Poly6 AmbientField (by simpa [toAmb] using h)
  exact hp (by simp [hp0])

private def IsLegalPred (z : AmbientField) : Prop :=
  ∃ a b : Poly6, residueMap b ≠ 0 ∧ z = toAmb a / toAmb b

def LegalAmb : Subring AmbientField where
  carrier := {z | IsLegalPred z}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, ?_⟩
    have h1 := toAmb_ne_of_residue_ne hb₁; have h2 := toAmb_ne_of_residue_ne hb₂
    simp only [map_add, map_mul]; field_simp [h1, h2]
  neg_mem' := by
    rintro x ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by rw [map_neg, ← neg_div]⟩
  mul_mem' := by
    rintro x y ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, ?_⟩
    simp only [map_mul]; ring

abbrev IsLegal (z : AmbientField) : Prop := z ∈ LegalAmb

lemma isLegal_toAmb (p : Poly6) : IsLegal (toAmb p) := ⟨p, 1, by simp, by simp⟩
lemma isLegal_zero : IsLegal 0 := LegalAmb.zero_mem
lemma isLegal_one : IsLegal 1 := LegalAmb.one_mem
lemma isLegal_add {x y : AmbientField} (hx : IsLegal x) (hy : IsLegal y) : IsLegal (x + y) :=
  LegalAmb.add_mem hx hy
lemma isLegal_neg {x : AmbientField} (hx : IsLegal x) : IsLegal (-x) :=
  LegalAmb.neg_mem hx
lemma isLegal_sub {x y : AmbientField} (hx : IsLegal x) (hy : IsLegal y) : IsLegal (x - y) :=
  LegalAmb.sub_mem hx hy
lemma isLegal_mul {x y : AmbientField} (hx : IsLegal x) (hy : IsLegal y) : IsLegal (x * y) :=
  LegalAmb.mul_mem hx hy
lemma isLegal_pow {x : AmbientField} (hx : IsLegal x) (k : ℕ) : IsLegal (x ^ k) :=
  LegalAmb.pow_mem hx k
lemma isLegal_sum {ι : Type*} (s : Finset ι) (f : ι → AmbientField)
    (hf : ∀ i ∈ s, IsLegal (f i)) : IsLegal (∑ i ∈ s, f i) :=
  LegalAmb.sum_mem hf

private lemma specX_well_defined {a₁ b₁ a₂ b₂ : Poly6}
    (hb₁ : residueMap b₁ ≠ 0) (hb₂ : residueMap b₂ ≠ 0)
    (heq : toAmb a₁ / toAmb b₁ = toAmb a₂ / toAmb b₂) :
    residueMap a₁ / residueMap b₁ = residueMap a₂ / residueMap b₂ := by
  have h1 := toAmb_ne_of_residue_ne hb₁; have h2 := toAmb_ne_of_residue_ne hb₂
  have hcross : a₁ * b₂ = a₂ * b₁ := by
    apply IsFractionRing.injective Poly6 AmbientField
    simpa only [toAmb, map_mul] using (div_eq_div_iff h1 h2).mp heq
  have hr := congrArg residueMap hcross
  simp only [map_mul] at hr
  exact (div_eq_div_iff hb₁ hb₂).mpr hr

def specXFun (z : LegalAmb) : FunctionField :=
  let a := Classical.choose z.property
  let b := Classical.choose (Classical.choose_spec z.property)
  residueMap a / residueMap b

lemma specXFun_eq (z : LegalAmb) {a b : Poly6} (hb : residueMap b ≠ 0)
    (heq : (z : AmbientField) = toAmb a / toAmb b) :
    specXFun z = residueMap a / residueMap b := by
  dsimp only [specXFun]
  exact specX_well_defined (Classical.choose_spec (Classical.choose_spec z.property)).1 hb
    ((Classical.choose_spec (Classical.choose_spec z.property)).2.symm.trans heq)

def specX : LegalAmb →+* FunctionField where
  toFun := specXFun
  map_one' := by
    rw [specXFun_eq 1 (a := 1) (b := 1) (by simp) (by simp)]; simp
  map_zero' := by
    rw [specXFun_eq 0 (a := 0) (b := 1) (by simp) (by simp)]; simp
  map_add' x y := by
    obtain ⟨a₁, b₁, hb₁, hx⟩ := x.property
    obtain ⟨a₂, b₂, hb₂, hy⟩ := y.property
    rw [specXFun_eq x hb₁ hx, specXFun_eq y hb₂ hy]
    have h1 := toAmb_ne_of_residue_ne hb₁; have h2 := toAmb_ne_of_residue_ne hb₂
    have hxy : ((x + y : LegalAmb) : AmbientField) = toAmb (a₁ * b₂ + a₂ * b₁) / toAmb (b₁ * b₂) := by
      change (x : AmbientField) + y = _
      rw [hx, hy]; simp only [map_add, map_mul]; field_simp [h1, h2]
    rw [specXFun_eq (x + y) (by rw [map_mul]; exact mul_ne_zero hb₁ hb₂) hxy]
    simp only [map_add, map_mul]; field_simp [hb₁, hb₂]
  map_mul' x y := by
    obtain ⟨a₁, b₁, hb₁, hx⟩ := x.property
    obtain ⟨a₂, b₂, hb₂, hy⟩ := y.property
    rw [specXFun_eq x hb₁ hx, specXFun_eq y hb₂ hy]
    have hxy : ((x * y : LegalAmb) : AmbientField) = toAmb (a₁ * a₂) / toAmb (b₁ * b₂) := by
      change (x : AmbientField) * y = _
      rw [hx, hy]; simp only [map_mul]; ring
    rw [specXFun_eq (x * y) (by rw [map_mul]; exact mul_ne_zero hb₁ hb₂) hxy]
    simp only [map_mul]; ring

lemma specX_toAmb (p : Poly6) {h : toAmb p ∈ LegalAmb} : specX ⟨toAmb p, h⟩ = residueMap p := by
  rw [specX, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    specXFun_eq ⟨toAmb p, h⟩ (a := p) (b := 1) (by simp) (by simp)]
  simp

lemma isLegal_ofNat (n : ℕ) [n.AtLeastTwo] :
    IsLegal (no_index (OfNat.ofNat n) : AmbientField) := by
  rw [← map_ofNat toAmb n]
  exact isLegal_toAmb _

lemma specX_ofNat (n : ℕ) [n.AtLeastTwo] {h : no_index (OfNat.ofNat n) ∈ LegalAmb} :
    specX ⟨no_index (OfNat.ofNat n), h⟩ = OfNat.ofNat n := by
  have heq : (⟨no_index (OfNat.ofNat n), h⟩ : LegalAmb) =
      ⟨toAmb (OfNat.ofNat n), isLegal_toAmb _⟩ := Subtype.ext (map_ofNat toAmb n).symm
  rw [heq, specX_toAmb, map_ofNat]

lemma specX_add {x y : AmbientField} {h : x + y ∈ LegalAmb} (hx : x ∈ LegalAmb) (hy : y ∈ LegalAmb) :
    specX ⟨x + y, h⟩ = specX ⟨x, hx⟩ + specX ⟨y, hy⟩ := by
  rw [show (⟨x + y, h⟩ : LegalAmb) = ⟨x, hx⟩ + ⟨y, hy⟩ from Subtype.ext rfl, map_add]

lemma specX_sub {x y : AmbientField} {h : x - y ∈ LegalAmb} (hx : x ∈ LegalAmb) (hy : y ∈ LegalAmb) :
    specX ⟨x - y, h⟩ = specX ⟨x, hx⟩ - specX ⟨y, hy⟩ := by
  rw [show (⟨x - y, h⟩ : LegalAmb) = ⟨x, hx⟩ - ⟨y, hy⟩ from Subtype.ext rfl, map_sub]

lemma specX_mul {x y : AmbientField} {h : x * y ∈ LegalAmb} (hx : x ∈ LegalAmb) (hy : y ∈ LegalAmb) :
    specX ⟨x * y, h⟩ = specX ⟨x, hx⟩ * specX ⟨y, hy⟩ := by
  rw [show (⟨x * y, h⟩ : LegalAmb) = ⟨x, hx⟩ * ⟨y, hy⟩ from Subtype.ext rfl, map_mul]

lemma specX_pow {x : AmbientField} {k : ℕ} {h : x ^ k ∈ LegalAmb} (hx : x ∈ LegalAmb) :
    specX ⟨x ^ k, h⟩ = specX ⟨x, hx⟩ ^ k := by
  rw [show (⟨x ^ k, h⟩ : LegalAmb) = ⟨x, hx⟩ ^ k from Subtype.ext rfl, map_pow]

lemma specX_neg {x : AmbientField} {h : -x ∈ LegalAmb} (hx : x ∈ LegalAmb) :
    specX ⟨-x, h⟩ = -specX ⟨x, hx⟩ := by
  rw [show (⟨-x, h⟩ : LegalAmb) = -⟨x, hx⟩ from Subtype.ext rfl, map_neg]

lemma isLegal_div {x y : AmbientField} (hx : IsLegal x) (hy : IsLegal y)
    (hy0 : specX ⟨y, hy⟩ ≠ 0) : IsLegal (x / y) := by
  obtain ⟨a₁, b₁, hb₁, rfl⟩ := hx
  obtain ⟨a₂, b₂, hb₂, rfl⟩ := hy
  have ha₂ : residueMap a₂ ≠ 0 := by
    intro h0
    apply hy0
    change specXFun ⟨toAmb a₂ / toAmb b₂, _⟩ = 0
    rw [specXFun_eq _ hb₂ rfl, h0, zero_div]
  refine ⟨a₁ * b₂, b₁ * a₂, by rw [map_mul]; exact mul_ne_zero hb₁ ha₂, ?_⟩
  have h1 := toAmb_ne_of_residue_ne hb₁; have h2 := toAmb_ne_of_residue_ne hb₂
  have h3 := toAmb_ne_of_residue_ne ha₂
  simp only [map_mul]; field_simp [h1, h2, h3]

lemma specX_div {x y : AmbientField} {h : x / y ∈ LegalAmb} (hx : x ∈ LegalAmb) (hy : y ∈ LegalAmb)
    (hy0 : specX ⟨y, hy⟩ ≠ 0) :
    specX ⟨x / y, h⟩ = specX ⟨x, hx⟩ / specX ⟨y, hy⟩ := by
  have hy_ne : y ≠ 0 := by
    intro h0; subst h0; apply hy0
    change specX 0 = 0; exact map_zero specX
  apply (eq_div_iff hy0).mpr
  rw [← map_mul]
  congr 1; apply Subtype.ext
  change x / y * y = x
  exact div_mul_cancel₀ x hy_ne

-- Ambient coordinate derivations
section AmbientCalculus
local instance : Algebra ℤ AmbientField := Ring.toIntAlgebra AmbientField

def D_amb (k : Fin 6) : Derivation ℤ AmbientField AmbientField :=
  HoldoutConstruction.extendRingDerivation (P := Poly6) (L := AmbientField)
    ((MvPolynomial.pderiv k : Derivation ℂ Poly6 Poly6).restrictScalars ℤ)

lemma D_amb_toAmb (k : Fin 6) (p : Poly6) :
    D_amb k (toAmb p) = toAmb (pderiv k p) :=
  HoldoutConstruction.extendRingDerivation_apply _ p

lemma D_amb_commute (i j : Fin 6) : Function.Commute (D_amb i) (D_amb j) := by
  apply HoldoutConstruction.extendRingDerivation_commute
  intro p
  change pderiv i (pderiv j p) = pderiv j (pderiv i p)
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, hp]
    have hc (a b : Fin 6) : pderiv a ((Pi.single b (1 : Poly6) : Fin 6 → Poly6) k) = 0 := by
      by_cases h : k = b
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    simp only [hc, mul_zero, zero_add]
    ring

lemma D_amb_isLegal (k : Fin 6) {z : AmbientField} (hz : IsLegal z) : IsLegal (D_amb k z) := by
  obtain ⟨a, b, hb, rfl⟩ := hz
  have hbA := toAmb_ne_of_residue_ne hb
  have hdiv : D_amb k (toAmb a / toAmb b) =
      toAmb (pderiv k a * b - a * pderiv k b) / toAmb (b ^ 2) := by
    rw [Derivation.leibniz_div, D_amb_toAmb, D_amb_toAmb]
    simp only [map_sub, map_mul, map_pow, smul_eq_mul]
    field_simp [hbA]
  exact ⟨pderiv k a * b - a * pderiv k b, b ^ 2, by rw [map_pow]; exact pow_ne_zero 2 hb, hdiv⟩

lemma D_amb_const (k : Fin 6) (c : ℂ) : D_amb k (toAmb (C c)) = 0 := by
  rw [D_amb_toAmb, pderiv_C, map_zero]

-- The 6 coordinates (Q_Y, S, Q, T, x, y) and W in AmbientField
abbrev QY_A : AmbientField := toAmb QY
abbrev e1X_A : AmbientField := toAmb e1X
abbrev QX_A : AmbientField := toAmb QX
abbrev e3X_A : AmbientField := toAmb e3X
abbrev e1Y_A : AmbientField := toAmb e1Y
abbrev e3Y_A : AmbientField := toAmb e3Y
abbrev ΔX_A : AmbientField := toAmb ΔX
abbrev ΔY_A : AmbientField := toAmb ΔY

def S_A : AmbientField := e1X_A ^ 2 / QY_A
def Q_A : AmbientField := QX_A / QY_A
def T_A : AmbientField := e1Y_A ^ 2 / QY_A
def u3_A : AmbientField := e3X_A / (e1X_A * QY_A)
def v3_A : AmbientField := e3Y_A / (e1Y_A * QY_A)
def x_A : AmbientField := u3_A + S_A - 2 * Q_A
def y_A : AmbientField := v3_A + T_A - 2
def W_A : AmbientField := e1X_A * ΔX_A * e1Y_A * ΔY_A / QY_A ^ 4

def coord6 : Fin 6 → AmbientField
  | 0 => QY_A
  | 1 => S_A
  | 2 => Q_A
  | 3 => T_A
  | 4 => x_A
  | 5 => y_A

def coord5 : Fin 5 → AmbientField
  | 0 => S_A
  | 1 => Q_A
  | 2 => T_A
  | 3 => x_A
  | 4 => y_A

def eval5_amb : Poly5 →+* AmbientField :=
  MvPolynomial.eval₂Hom (toAmb.comp MvPolynomial.C) coord5

lemma e1X_A_ne : e1X_A ≠ 0 := toAmb_ne_of_residue_ne residueMap_e1X_ne
lemma e1Y_A_ne : e1Y_A ≠ 0 := toAmb_ne_of_residue_ne residueMap_e1Y_ne
lemma QY_A_ne  : QY_A  ≠ 0 := toAmb_ne_of_residue_ne residueMap_QY_ne
lemma ΔX_A_ne  : ΔX_A  ≠ 0 := toAmb_ne_of_residue_ne residueMap_ΔX_ne
lemma ΔY_A_ne  : ΔY_A  ≠ 0 := toAmb_ne_of_residue_ne residueMap_ΔY_ne

lemma eval5_amb_u3 : eval5_amb u3_5 = u3_A := by
  simp only [u3_5, eval5_amb, map_sub, map_add, map_mul, map_ofNat, eval₂Hom_X', coord5, x_A]
  ring

lemma eval5_amb_v3 : eval5_amb v3_5 = v3_A := by
  simp only [v3_5, eval5_amb, map_sub, map_add, map_ofNat, eval₂Hom_X', coord5, y_A]
  ring

lemma F6_eq_QY3_F5 : toAmb sextic = QY_A ^ 3 * eval5_amb F5 := by
  have he1X : toAmb (X 0) + toAmb (X 1) + toAmb (X 2) = e1X_A := by simp [e1X_A, e1X]
  have hQX : toAmb (X 0) * toAmb (X 1) + toAmb (X 0) * toAmb (X 2) + toAmb (X 1) * toAmb (X 2) = QX_A := by
    simp [QX_A, QX]
  have he3X : toAmb (X 0) * toAmb (X 1) * toAmb (X 2) = e3X_A := by simp [e3X_A, e3X]
  have he1Y : toAmb (X 3) + toAmb (X 4) + toAmb (X 5) = e1Y_A := by simp [e1Y_A, e1Y]
  have hQY : toAmb (X 3) * toAmb (X 4) + toAmb (X 3) * toAmb (X 5) + toAmb (X 4) * toAmb (X 5) = QY_A := by
    simp [QY_A, QY]
  have he3Y : toAmb (X 3) * toAmb (X 4) * toAmb (X 5) = e3Y_A := by simp [e3Y_A, e3Y]
  have hx6 := sum_sixth_eq_sym (toAmb (X 0)) (toAmb (X 1)) (toAmb (X 2))
  have hy6 := sum_sixth_eq_sym (toAmb (X 3)) (toAmb (X 4)) (toAmb (X 5))
  dsimp only at hx6 hy6
  rw [he1X, hQX, he3X] at hx6
  rw [he1Y, hQY, he3Y] at hy6
  have hF6 : toAmb sextic =
      (toAmb (X 0) ^ 6 + toAmb (X 1) ^ 6 + toAmb (X 2) ^ 6) +
      (toAmb (X 3) ^ 6 + toAmb (X 4) ^ 6 + toAmb (X 5) ^ 6) +
      toAmb (C (5 / 7 : ℂ)) * QX_A ^ 2 * QY_A + toAmb (C (10 / 7 : ℂ)) * QX_A * QY_A ^ 2 := by
    simp only [sextic, QX_A, QY_A, map_add, map_mul, map_pow]; ring
  rw [hF6, hx6, hy6, F5_eq_u3_v3]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  rw [eval5_amb_u3, eval5_amb_v3]
  simp only [eval5_amb, eval₂Hom_X', eval₂Hom_C, RingHom.comp_apply, coord5, S_A, Q_A, T_A, u3_A, v3_A]
  have h1 := e1X_A_ne; have h2 := e1Y_A_ne; have h3 := QY_A_ne
  generalize e1X_A = a1 at h1 ⊢; generalize QX_A = a2; generalize e3X_A = a3
  generalize e1Y_A = b1 at h2 ⊢; generalize QY_A = b2 at h3 ⊢; generalize e3Y_A = b3
  generalize toAmb (C (5 / 7 : ℂ)) = c5; generalize toAmb (C (10 / 7 : ℂ)) = c10
  field_simp [h1, h2, h3]
  ring

lemma W_A_sq : W_A ^ 2 = eval5_amb W2_5 := by
  have he1X : toAmb (X 0) + toAmb (X 1) + toAmb (X 2) = e1X_A := by simp [e1X_A, e1X]
  have hQX : toAmb (X 0) * toAmb (X 1) + toAmb (X 0) * toAmb (X 2) + toAmb (X 1) * toAmb (X 2) = QX_A := by
    simp [QX_A, QX]
  have he3X : toAmb (X 0) * toAmb (X 1) * toAmb (X 2) = e3X_A := by simp [e3X_A, e3X]
  have hΔX : (toAmb (X 0) - toAmb (X 1)) * (toAmb (X 0) - toAmb (X 2)) * (toAmb (X 1) - toAmb (X 2)) = ΔX_A := by
    simp [ΔX_A, ΔX]
  have he1Y : toAmb (X 3) + toAmb (X 4) + toAmb (X 5) = e1Y_A := by simp [e1Y_A, e1Y]
  have hQY : toAmb (X 3) * toAmb (X 4) + toAmb (X 3) * toAmb (X 5) + toAmb (X 4) * toAmb (X 5) = QY_A := by
    simp [QY_A, QY]
  have he3Y : toAmb (X 3) * toAmb (X 4) * toAmb (X 5) = e3Y_A := by simp [e3Y_A, e3Y]
  have hΔY : (toAmb (X 3) - toAmb (X 4)) * (toAmb (X 3) - toAmb (X 5)) * (toAmb (X 4) - toAmb (X 5)) = ΔY_A := by
    simp [ΔY_A, ΔY]
  have hdx := disc_sq_eq_sym (toAmb (X 0)) (toAmb (X 1)) (toAmb (X 2))
  have hdy := disc_sq_eq_sym (toAmb (X 3)) (toAmb (X 4)) (toAmb (X 5))
  dsimp only at hdx hdy
  rw [he1X, hQX, he3X, hΔX] at hdx
  rw [he1Y, hQY, he3Y, hΔY] at hdy
  have hDX : eval5_amb DX2_5 = ΔX_A ^ 2 / QY_A ^ 3 := by
    rw [DX2_5]; simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [eval5_amb_u3]
    simp only [eval5_amb, eval₂Hom_X', coord5, S_A, Q_A, u3_A]
    rw [hdx]; have h1 := e1X_A_ne; have h3 := QY_A_ne
    generalize e1X_A = a1 at h1 ⊢; generalize QX_A = a2; generalize e3X_A = a3
    generalize QY_A = b2 at h3 ⊢
    field_simp [h1, h3]
  have hDY : eval5_amb DY2_5 = ΔY_A ^ 2 / QY_A ^ 3 := by
    rw [DY2_5]; simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [eval5_amb_v3]
    simp only [eval5_amb, eval₂Hom_X', coord5, T_A, v3_A]
    rw [hdy]; have h2 := e1Y_A_ne; have h3 := QY_A_ne
    generalize e1Y_A = b1 at h2 ⊢; generalize QY_A = b2 at h3 ⊢; generalize e3Y_A = b3
    field_simp [h2, h3]
  rw [W2_5, map_mul, map_mul, map_mul, hDX, hDY]
  simp only [eval5_amb, eval₂Hom_X', coord5, W_A, S_A, T_A]
  have h3 := QY_A_ne; field_simp [h3]

lemma MA_over_W : eval5_amb MA_5 / W_A = toAmb source / (ΔX_A * ΔY_A) := by
  have hMA : eval5_amb MA_5 = e1X_A * e3X_A * e1Y_A * e3Y_A / QY_A ^ 4 := by
    rw [MA_5]; simp only [map_mul]; rw [eval5_amb_u3, eval5_amb_v3]
    simp only [eval5_amb, eval₂Hom_X', coord5, S_A, T_A, u3_A, v3_A]
    have h1 := e1X_A_ne; have h2 := e1Y_A_ne; have h3 := QY_A_ne; field_simp [h1, h2, h3]
  have hsrc : toAmb source = e3X_A * e3Y_A := by simp [source, e3X_A, e3Y_A]
  rw [hMA, hsrc, W_A]
  have h1 := e1X_A_ne; have h2 := e1Y_A_ne; have h3 := QY_A_ne
  have h4 := ΔX_A_ne; have h5 := ΔY_A_ne
  field_simp [h1, h2, h3, h4, h5]

-- 2-step block Jacobian M = M_outer * M_inner and explicit inverse N = N_inner * N_outer
def jac3 {K : Type*} [Field K] (a b c : K) : Matrix (Fin 3) (Fin 3) K
  | 0, 0 => 1 | 0, 1 => 1 | 0, 2 => 1
  | 1, 0 => b + c | 1, 1 => a + c | 1, 2 => a + b
  | 2, 0 => b * c | 2, 1 => a * c | 2, 2 => a * b

def invJac3 {K : Type*} [Field K] (a b c : K) : Matrix (Fin 3) (Fin 3) K
  | 0, 0 => a ^ 2 * (b - c) / ((a - b) * (a - c) * (b - c))
  | 0, 1 => -(a * (b - c)) / ((a - b) * (a - c) * (b - c))
  | 0, 2 => (b - c) / ((a - b) * (a - c) * (b - c))
  | 1, 0 => b ^ 2 * (c - a) / ((a - b) * (a - c) * (b - c))
  | 1, 1 => -(b * (c - a)) / ((a - b) * (a - c) * (b - c))
  | 1, 2 => (c - a) / ((a - b) * (a - c) * (b - c))
  | 2, 0 => c ^ 2 * (a - b) / ((a - b) * (a - c) * (b - c))
  | 2, 1 => -(c * (a - b)) / ((a - b) * (a - c) * (b - c))
  | 2, 2 => (a - b) / ((a - b) * (a - c) * (b - c))

lemma jac3_det {K : Type*} [Field K] (a b c : K) :
    (jac3 a b c).det = (a - b) * (a - c) * (b - c) := by
  simp [jac3, Matrix.det_fin_three]; ring

lemma jac3_mul_inv {K : Type*} [Field K] (a b c : K) (hd : (a - b) * (a - c) * (b - c) ≠ 0) :
    jac3 a b c * invJac3 a b c = 1 := by
  have hab : a - b ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hac : a - c ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hbc : b - c ≠ 0 := right_ne_zero_of_mul hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, jac3, invJac3];
     split_ifs with h
     · first | exact absurd h (by decide) | field
     · field)

lemma inv_mul_jac3 {K : Type*} [Field K] (a b c : K) (hd : (a - b) * (a - c) * (b - c) ≠ 0) :
    invJac3 a b c * jac3 a b c = 1 := by
  have hab : a - b ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hac : a - c ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hbc : b - c ≠ 0 := right_ne_zero_of_mul hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, jac3, invJac3];
     split_ifs with h
     · first | exact absurd h (by decide) | field
     · field)

private def fin6Equiv : Fin 6 ≃ Fin 3 ⊕ Fin 3 :=
  { toFun := fun i => if h : i.val < 3 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 3, by omega⟩
    invFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun i => ⟨i.val + 3, by omega⟩)
    left_inv := fun i => by fin_cases i <;> rfl
    right_inv := fun x => by rcases x with i | i <;> fin_cases i <;> rfl }

def M_inner : Matrix (Fin 6) (Fin 6) AmbientField :=
  (Matrix.fromBlocks (jac3 (toAmb (X 0)) (toAmb (X 1)) (toAmb (X 2))) 0 0
    (jac3 (toAmb (X 3)) (toAmb (X 4)) (toAmb (X 5)))).reindex fin6Equiv.symm fin6Equiv.symm

def N_inner : Matrix (Fin 6) (Fin 6) AmbientField :=
  (Matrix.fromBlocks (invJac3 (toAmb (X 0)) (toAmb (X 1)) (toAmb (X 2))) 0 0
    (invJac3 (toAmb (X 3)) (toAmb (X 4)) (toAmb (X 5)))).reindex fin6Equiv.symm fin6Equiv.symm

lemma M_inner_det : M_inner.det = ΔX_A * ΔY_A := by
  rw [M_inner, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂, jac3_det, jac3_det]
  have h1 : (toAmb (X 0) - toAmb (X 1)) * (toAmb (X 0) - toAmb (X 2)) * (toAmb (X 1) - toAmb (X 2)) = ΔX_A := by
    simp [ΔX_A, ΔX]
  have h2 : (toAmb (X 3) - toAmb (X 4)) * (toAmb (X 3) - toAmb (X 5)) * (toAmb (X 4) - toAmb (X 5)) = ΔY_A := by
    simp [ΔY_A, ΔY]
  rw [h1, h2]

private lemma reindex_fin6_mul (A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) AmbientField) :
    A.reindex fin6Equiv.symm fin6Equiv.symm * B.reindex fin6Equiv.symm fin6Equiv.symm =
      (A * B).reindex fin6Equiv.symm fin6Equiv.symm := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  exact (Equiv.sum_comp fin6Equiv (fun k => A (fin6Equiv i) k * B k (fin6Equiv j))).symm

lemma M_inner_mul_N_inner : M_inner * N_inner = 1 := by
  have h1 : (toAmb (X 0) - toAmb (X 1)) * (toAmb (X 0) - toAmb (X 2)) * (toAmb (X 1) - toAmb (X 2)) ≠ 0 := by
    simpa [ΔX_A, ΔX] using ΔX_A_ne
  have h2 : (toAmb (X 3) - toAmb (X 4)) * (toAmb (X 3) - toAmb (X 5)) * (toAmb (X 4) - toAmb (X 5)) ≠ 0 := by
    simpa [ΔY_A, ΔY] using ΔY_A_ne
  rw [M_inner, N_inner, reindex_fin6_mul, Matrix.fromBlocks_multiply,
    jac3_mul_inv _ _ _ h1, jac3_mul_inv _ _ _ h2]
  simp [Matrix.fromBlocks_one]

lemma N_inner_mul_M_inner : N_inner * M_inner = 1 := by
  have h1 : (toAmb (X 0) - toAmb (X 1)) * (toAmb (X 0) - toAmb (X 2)) * (toAmb (X 1) - toAmb (X 2)) ≠ 0 := by
    simpa [ΔX_A, ΔX] using ΔX_A_ne
  have h2 : (toAmb (X 3) - toAmb (X 4)) * (toAmb (X 3) - toAmb (X 5)) * (toAmb (X 4) - toAmb (X 5)) ≠ 0 := by
    simpa [ΔY_A, ΔY] using ΔY_A_ne
  rw [M_inner, N_inner, reindex_fin6_mul, Matrix.fromBlocks_multiply,
    inv_mul_jac3 _ _ _ h1, inv_mul_jac3 _ _ _ h2]
  simp [Matrix.fromBlocks_one]

def mOuter6 {K : Type*} [Field K] (a1 a2 a3 b1 b2 b3 : K) : Matrix (Fin 6) (Fin 6) K :=
  fun i j => match i.val with
  | 0 => match j.val with | 4 => 1 | _ => 0
  | 1 => match j.val with | 0 => 2 * a1 / b2 | 4 => -(a1 ^ 2 / b2 ^ 2) | _ => 0
  | 2 => match j.val with | 1 => 1 / b2 | 4 => -(a2 / b2 ^ 2) | _ => 0
  | 3 => match j.val with | 3 => 2 * b1 / b2 | 4 => -(b1 ^ 2 / b2 ^ 2) | _ => 0
  | 4 => match j.val with
    | 0 => -(a3 / (a1 ^ 2 * b2)) + 2 * a1 / b2
    | 1 => -(2 / b2) | 2 => 1 / (a1 * b2)
    | 4 => -(a3 / (a1 * b2 ^ 2)) - a1 ^ 2 / b2 ^ 2 + 2 * a2 / b2 ^ 2
    | _ => 0
  | _ => match j.val with
    | 3 => -(b3 / (b1 ^ 2 * b2)) + 2 * b1 / b2
    | 4 => -(b3 / (b1 * b2 ^ 2)) - b1 ^ 2 / b2 ^ 2
    | 5 => 1 / (b1 * b2)
    | _ => 0

def nOuter6 {K : Type*} [Field K] (a1 a2 a3 b1 b2 b3 : K) : Matrix (Fin 6) (Fin 6) K :=
  fun i j => match i.val with
  | 0 => match j.val with | 0 => a1 / (2 * b2) | 1 => b2 / (2 * a1) | _ => 0
  | 1 => match j.val with | 0 => a2 / b2 | 2 => b2 | _ => 0
  | 2 => match j.val with
    | 0 => 3 * a3 / (2 * b2) | 1 => (-2 * a1 ^ 3 + a3) * b2 / (2 * a1 ^ 2)
    | 2 => 2 * a1 * b2 | 4 => a1 * b2 | _ => 0
  | 3 => match j.val with | 0 => b1 / (2 * b2) | 3 => b2 / (2 * b1) | _ => 0
  | 4 => match j.val with | 0 => 1 | _ => 0
  | _ => match j.val with
    | 0 => 3 * b3 / (2 * b2) | 3 => (-2 * b1 ^ 3 + b3) * b2 / (2 * b1 ^ 2)
    | 5 => b1 * b2 | _ => 0

lemma mOuter6_mul_nOuter6 {K : Type*} [Field K] [CharZero K]
    (a1 a2 a3 b1 b2 b3 : K) (h1 : a1 ≠ 0) (h2 : b1 ≠ 0) (h3 : b2 ≠ 0) :
    mOuter6 a1 a2 a3 b1 b2 b3 * nOuter6 a1 a2 a3 b1 b2 b3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_six];
     dsimp [mOuter6, nOuter6];
     simp only [mul_zero, zero_mul, add_zero, zero_add]) <;>
    field

lemma nOuter6_mul_mOuter6 {K : Type*} [Field K] [CharZero K]
    (a1 a2 a3 b1 b2 b3 : K) (h1 : a1 ≠ 0) (h2 : b1 ≠ 0) (h3 : b2 ≠ 0) :
    nOuter6 a1 a2 a3 b1 b2 b3 * mOuter6 a1 a2 a3 b1 b2 b3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_six];
     dsimp [mOuter6, nOuter6];
     simp only [mul_zero, zero_mul, add_zero, zero_add]) <;>
    field

def M_outer : Matrix (Fin 6) (Fin 6) AmbientField :=
  mOuter6 e1X_A QX_A e3X_A e1Y_A QY_A e3Y_A

def N_outer : Matrix (Fin 6) (Fin 6) AmbientField :=
  nOuter6 e1X_A QX_A e3X_A e1Y_A QY_A e3Y_A

lemma M_outer_mul_N_outer : M_outer * N_outer = 1 :=
  mOuter6_mul_nOuter6 _ _ _ _ _ _ e1X_A_ne e1Y_A_ne QY_A_ne

lemma N_outer_mul_M_outer : N_outer * M_outer = 1 :=
  nOuter6_mul_mOuter6 _ _ _ _ _ _ e1X_A_ne e1Y_A_ne QY_A_ne

private def permTri : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective ![4, 0, 1, 3, 2, 5] (by decide)

lemma N_outer_det : N_outer.det = -(QY_A ^ 5 / 4) := by
  let L : Matrix (Fin 6) (Fin 6) AmbientField := N_outer.submatrix permTri id
  have hlt : L.IsLowerTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | rfl
  have hdetL : L.det = QY_A ^ 5 / 4 := by
    rw [Matrix.det_of_isLowerTriangular L hlt, Fin.prod_univ_six]
    change 1 * (QY_A / (2 * e1X_A)) * QY_A * (QY_A / (2 * e1Y_A)) * (e1X_A * QY_A) * (e1Y_A * QY_A) = QY_A ^ 5 / 4
    have h1 := e1X_A_ne; have h2 := e1Y_A_ne
    generalize e1X_A = a1 at h1 ⊢; generalize e1Y_A = b1 at h2 ⊢; generalize QY_A = b2
    calc
      1 * (b2 / (2 * a1)) * b2 * (b2 / (2 * b1)) * (a1 * b2) * (b1 * b2)
          = (b2 ^ 5 / 4) * (a1 / a1) * (b1 / b1) := by ring
      _ = b2 ^ 5 / 4 := by rw [div_self h1, div_self h2]; ring
  have hperm : L.det = (Equiv.Perm.sign permTri : ℤ) * N_outer.det := by
    simpa [L, Matrix.submatrix_id_id] using Matrix.det_permute permTri N_outer
  have hsgn : Equiv.Perm.sign permTri = -1 := by decide
  rw [hsgn, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hperm
  linear_combination hperm - hdetL

lemma M_outer_det : M_outer.det = -(4 / QY_A ^ 5) := by
  have hmul : M_outer.det * N_outer.det = 1 := by
    rw [← Matrix.det_mul, M_outer_mul_N_outer, Matrix.det_one]
  rw [N_outer_det] at hmul
  have h3 := QY_A_ne
  have hq5 : -(QY_A ^ 5 / 4) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 5 h3) (by norm_num))
  apply mul_right_cancel₀ hq5
  rw [hmul]; field_simp [h3]

def M_jac : Matrix (Fin 6) (Fin 6) AmbientField := M_outer * M_inner
def N_jac : Matrix (Fin 6) (Fin 6) AmbientField := N_inner * N_outer

lemma M_mul_N : M_jac * N_jac = 1 := by
  rw [M_jac, N_jac, Matrix.mul_assoc, ← Matrix.mul_assoc M_inner, M_inner_mul_N_inner,
    Matrix.one_mul, M_outer_mul_N_outer]

lemma N_mul_M : N_jac * M_jac = 1 := by
  rw [M_jac, N_jac, Matrix.mul_assoc, ← Matrix.mul_assoc N_outer, N_outer_mul_M_outer,
    Matrix.one_mul, N_inner_mul_M_inner]

lemma M_jac_det : M_jac.det = -4 * ΔX_A * ΔY_A / QY_A ^ 5 := by
  rw [M_jac, Matrix.det_mul, M_outer_det, M_inner_det]; ring

lemma M_jac_det_ne : M_jac.det ≠ 0 := by
  rw [M_jac_det]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ΔX_A_ne) ΔY_A_ne)
    (pow_ne_zero 5 QY_A_ne)

lemma M_jac_entry (j k : Fin 6) : M_jac j k = D_amb k (coord6 j) := by
  have h1 := e1X_A_ne; have h2 := e1Y_A_ne; have h3 := QY_A_ne
  have h0 (k : Fin 6) : D_amb k e1X_A = M_inner 0 k := by
    rw [e1X_A, e1X, D_amb_toAmb]
    fin_cases k <;>
      (simp only [map_add, pderiv_X, Pi.single_apply, Fin.isValue];
       dsimp [M_inner, fin6Equiv, jac3]; simp)
  have h3' (k : Fin 6) : D_amb k e1Y_A = M_inner 3 k := by
    rw [e1Y_A, e1Y, D_amb_toAmb]
    fin_cases k <;>
      (simp only [map_add, pderiv_X, Pi.single_apply, Fin.isValue];
       dsimp [M_inner, fin6Equiv, jac3]; simp)
  have hQX (k : Fin 6) : D_amb k QX_A = M_inner 1 k := by
    rw [QX_A, QX, D_amb_toAmb]
    fin_cases k <;>
      (simp only [map_add, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Fin.isValue];
       dsimp [M_inner, fin6Equiv, jac3]; simp)
  have hQY (k : Fin 6) : D_amb k QY_A = M_inner 4 k := by
    rw [QY_A, QY, D_amb_toAmb]
    fin_cases k <;>
      (simp only [map_add, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Fin.isValue];
       dsimp [M_inner, fin6Equiv, jac3]; simp)
  have he3X (k : Fin 6) : D_amb k e3X_A = M_inner 2 k := by
    rw [e3X_A, e3X, D_amb_toAmb]
    fin_cases k <;>
      (simp only [Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Fin.isValue];
       dsimp [M_inner, fin6Equiv, jac3]; simp [mul_comm])
  have he3Y (k : Fin 6) : D_amb k e3Y_A = M_inner 5 k := by
    rw [e3Y_A, e3Y, D_amb_toAmb]
    fin_cases k <;>
      (simp only [Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Fin.isValue];
       dsimp [M_inner, fin6Equiv, jac3]; simp [mul_comm])
  fin_cases j
  · simp only [M_jac, Matrix.mul_apply, Fin.sum_univ_six, coord6, hQY]
    dsimp [M_outer, mOuter6]
    simp only [zero_mul, one_mul, add_zero, zero_add]
  · simp only [M_jac, Matrix.mul_apply, Fin.sum_univ_six, coord6, S_A,
      Derivation.leibniz_div, Derivation.leibniz_pow, h0, hQY, smul_eq_mul, nsmul_eq_mul]
    dsimp [M_outer, mOuter6]
    simp only [zero_mul, add_zero]
    generalize e1X_A = a1; generalize QY_A = b2 at h3 ⊢
    generalize M_inner 0 k = m0; generalize M_inner 4 k = m4
    field
  · simp only [M_jac, Matrix.mul_apply, Fin.sum_univ_six, coord6, Q_A,
      Derivation.leibniz_div, hQX, hQY, smul_eq_mul]
    dsimp [M_outer, mOuter6]
    simp only [zero_mul, add_zero, zero_add]
    generalize QX_A = a2; generalize QY_A = b2 at h3 ⊢
    generalize M_inner 1 k = m1; generalize M_inner 4 k = m4
    field
  · simp only [M_jac, Matrix.mul_apply, Fin.sum_univ_six, coord6, T_A,
      Derivation.leibniz_div, Derivation.leibniz_pow, h3', hQY, smul_eq_mul, nsmul_eq_mul]
    dsimp [M_outer, mOuter6]
    simp only [zero_mul, add_zero, zero_add]
    generalize e1Y_A = b1; generalize QY_A = b2 at h3 ⊢
    generalize M_inner 3 k = m3; generalize M_inner 4 k = m4
    field
  · simp only [M_jac, Matrix.mul_apply, Fin.sum_univ_six, coord6, x_A, u3_A, S_A, Q_A,
      map_sub, map_add, Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
      h0, hQX, he3X, hQY, smul_eq_mul, nsmul_eq_mul]
    dsimp [M_outer, mOuter6]
    simp only [zero_mul, add_zero]
    have h20 : D_amb k (2 : AmbientField) = 0 := by
      rw [show (2 : AmbientField) = 1 + 1 by norm_num, map_add, Derivation.map_one_eq_zero, add_zero]
    rw [h20]
    generalize e1X_A = a1 at h1 ⊢; generalize QX_A = a2; generalize e3X_A = a3
    generalize QY_A = b2 at h3 ⊢
    generalize M_inner 0 k = m0; generalize M_inner 1 k = m1
    generalize M_inner 2 k = m2; generalize M_inner 4 k = m4
    field
  · simp only [M_jac, Matrix.mul_apply, Fin.sum_univ_six, coord6, y_A, v3_A, T_A,
      map_sub, map_add, Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
      h3', he3Y, hQY, smul_eq_mul, nsmul_eq_mul]
    dsimp [M_outer, mOuter6]
    simp only [zero_mul, add_zero, zero_add]
    have h20 : D_amb k (2 : AmbientField) = 0 := by
      rw [show (2 : AmbientField) = 1 + 1 by norm_num, map_add, Derivation.map_one_eq_zero, add_zero]
    rw [h20]
    generalize e1Y_A = b1 at h2 ⊢; generalize QY_A = b2 at h3 ⊢; generalize e3Y_A = b3
    generalize M_inner 3 k = m3; generalize M_inner 4 k = m4; generalize M_inner 5 k = m5
    field

lemma M_jac_mixed (i j k : Fin 6) : D_amb k (M_jac j i) = D_amb i (M_jac j k) := by
  rw [M_jac_entry, M_jac_entry]; exact D_amb_commute k i (coord6 j)

-- Dual coordinate derivations E_amb on AmbientField
def E_amb (j : Fin 6) : Derivation ℤ AmbientField AmbientField :=
  ∑ k : Fin 6, (N_jac k j) • D_amb k

lemma E_amb_apply (j : Fin 6) (z : AmbientField) :
    E_amb j z = ∑ k : Fin 6, N_jac k j * D_amb k z := by
  dsimp only [E_amb]
  rw [Fin.sum_univ_six, Fin.sum_univ_six]
  simp only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

lemma E_amb_coord6 (j i : Fin 6) : E_amb j (coord6 i) = if i = j then 1 else 0 := by
  rw [E_amb_apply]
  have h := congrFun (congrFun M_mul_N i) j
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  apply Finset.sum_congr rfl; intro k _
  rw [M_jac_entry, mul_comm]

lemma E_amb_const (j : Fin 6) (c : ℂ) : E_amb j (toAmb (C c)) = 0 := by
  rw [E_amb_apply]
  apply Finset.sum_eq_zero; intro k _; rw [D_amb_const, mul_zero]

lemma E_amb_zero_eval5 (p : Poly5) : E_amb 0 (eval5_amb p) = 0 := by
  have hc := HoldoutConstruction.derivation_eval₂_chain (E_amb 0)
    (toAmb.comp MvPolynomial.C) coord5 (fun c => E_amb_const 0 c) p
  change E_amb 0 (eval5_amb p) = ∑ i : Fin 5, eval5_amb (pderiv i p) * E_amb 0 (coord5 i) at hc
  rw [hc]
  apply Finset.sum_eq_zero; intro i _
  have hci : coord5 i = coord6 i.succ := by fin_cases i <;> rfl
  rw [hci, E_amb_coord6, if_neg (Fin.succ_ne_zero i), mul_zero]

lemma E_amb_succ_eval5 (j : Fin 5) (p : Poly5) :
    E_amb j.succ (eval5_amb p) = eval5_amb (pderiv j p) := by
  have hc := HoldoutConstruction.derivation_eval₂_chain (E_amb j.succ)
    (toAmb.comp MvPolynomial.C) coord5 (fun c => E_amb_const j.succ c) p
  change E_amb j.succ (eval5_amb p) = ∑ i : Fin 5, eval5_amb (pderiv i p) * E_amb j.succ (coord5 i) at hc
  rw [hc, Finset.sum_eq_single j]
  · have hcj : coord5 j = coord6 j.succ := by fin_cases j <;> rfl
    rw [hcj, E_amb_coord6, if_pos rfl, mul_one]
  · intro i _ hij
    have hci : coord5 i = coord6 i.succ := by fin_cases i <;> rfl
    rw [hci, E_amb_coord6, if_neg (fun h => hij (Fin.succ_injective _ h)), mul_zero]
  · intro h; exact (h (Finset.mem_univ j)).elim

lemma W_A_ne : W_A ≠ 0 := by
  rw [W_A]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero e1X_A_ne ΔX_A_ne) e1Y_A_ne) ΔY_A_ne)
    (pow_ne_zero 4 QY_A_ne)

lemma E_amb_zero_W : E_amb 0 W_A = 0 := by
  have h := congrArg (E_amb 0) W_A_sq
  rw [Derivation.leibniz_pow, E_amb_zero_eval5] at h
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at h
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one] at h
  exact (mul_eq_zero.mp (mul_eq_zero.mp h |>.resolve_left (by norm_num))).resolve_left W_A_ne

lemma E_amb_succ_W (j : Fin 5) :
    E_amb j.succ W_A = W_A * eval5_amb (pderiv j W2_5) / (2 * eval5_amb W2_5) := by
  have h := congrArg (E_amb j.succ) W_A_sq
  rw [Derivation.leibniz_pow, E_amb_succ_eval5] at h
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at h
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one] at h
  have h2W : (2 * eval5_amb W2_5 : AmbientField) ≠ 0 := by
    rw [← W_A_sq]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 W_A_ne)
  apply (eq_div_iff h2W).mpr
  rw [← W_A_sq]
  linear_combination W_A * h

-- Legality of coordinates, matrices, and tangent descent to FunctionField
private lemma specX_QY_ne : specX ⟨QY_A, isLegal_toAmb QY⟩ ≠ 0 := by
  have h : specX ⟨QY_A, isLegal_toAmb QY⟩ = residueMap QY := specX_toAmb QY
  rw [h]; exact residueMap_QY_ne
private lemma specX_e1X_ne : specX ⟨e1X_A, isLegal_toAmb e1X⟩ ≠ 0 := by
  have h : specX ⟨e1X_A, isLegal_toAmb e1X⟩ = residueMap e1X := specX_toAmb e1X
  rw [h]; exact residueMap_e1X_ne
private lemma specX_e1Y_ne : specX ⟨e1Y_A, isLegal_toAmb e1Y⟩ ≠ 0 := by
  have h : specX ⟨e1Y_A, isLegal_toAmb e1Y⟩ = residueMap e1Y := specX_toAmb e1Y
  rw [h]; exact residueMap_e1Y_ne
private lemma specX_ΔX_ne : specX ⟨ΔX_A, isLegal_toAmb ΔX⟩ ≠ 0 := by
  have h : specX ⟨ΔX_A, isLegal_toAmb ΔX⟩ = residueMap ΔX := specX_toAmb ΔX
  rw [h]; exact residueMap_ΔX_ne
private lemma specX_ΔY_ne : specX ⟨ΔY_A, isLegal_toAmb ΔY⟩ ≠ 0 := by
  have h : specX ⟨ΔY_A, isLegal_toAmb ΔY⟩ = residueMap ΔY := specX_toAmb ΔY
  rw [h]; exact residueMap_ΔY_ne

lemma coord6_isLegal (i : Fin 6) : IsLegal (coord6 i) := by
  have hQY := specX_QY_ne; have he1X := specX_e1X_ne; have he1Y := specX_e1Y_ne
  have h1 : IsLegal (e1X_A * QY_A) := isLegal_mul (isLegal_toAmb e1X) (isLegal_toAmb QY)
  have h1ne : specX ⟨e1X_A * QY_A, h1⟩ ≠ 0 := by
    rw [specX_mul (isLegal_toAmb e1X) (isLegal_toAmb QY)]; exact mul_ne_zero he1X hQY
  have h2 : IsLegal (e1Y_A * QY_A) := isLegal_mul (isLegal_toAmb e1Y) (isLegal_toAmb QY)
  have h2ne : specX ⟨e1Y_A * QY_A, h2⟩ ≠ 0 := by
    rw [specX_mul (isLegal_toAmb e1Y) (isLegal_toAmb QY)]; exact mul_ne_zero he1Y hQY
  fin_cases i
  · exact isLegal_toAmb QY
  · exact isLegal_div (isLegal_pow (isLegal_toAmb _) 2) (isLegal_toAmb _) hQY
  · exact isLegal_div (isLegal_toAmb _) (isLegal_toAmb _) hQY
  · exact isLegal_div (isLegal_pow (isLegal_toAmb _) 2) (isLegal_toAmb _) hQY
  · exact isLegal_sub
      (isLegal_add (isLegal_div (isLegal_toAmb _) h1 h1ne)
        (isLegal_div (isLegal_pow (isLegal_toAmb _) 2) (isLegal_toAmb _) hQY))
      (isLegal_mul (isLegal_ofNat 2) (isLegal_div (isLegal_toAmb _) (isLegal_toAmb _) hQY))
  · exact isLegal_sub
      (isLegal_add (isLegal_div (isLegal_toAmb _) h2 h2ne)
        (isLegal_div (isLegal_pow (isLegal_toAmb _) 2) (isLegal_toAmb _) hQY))
      (isLegal_ofNat 2)

lemma eval5_amb_isLegal (p : Poly5) : IsLegal (eval5_amb p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [eval5_amb, eval₂Hom_C, RingHom.comp_apply]; exact isLegal_toAmb (C c)
  | add p q hp hq => rw [map_add]; exact isLegal_add hp hq
  | mul_X p i hp =>
    rw [map_mul]; apply isLegal_mul hp
    have hci : eval5_amb (X i) = coord6 i.succ := by fin_cases i <;> simp [eval5_amb, coord5, coord6]
    rw [hci]; exact coord6_isLegal i.succ

lemma W_A_isLegal : IsLegal W_A := by
  have hQY4 : specX ⟨QY_A ^ 4, isLegal_pow (isLegal_toAmb QY) 4⟩ ≠ 0 := by
    rw [specX_pow (isLegal_toAmb QY)]; exact pow_ne_zero 4 specX_QY_ne
  exact isLegal_div
    (isLegal_mul (isLegal_mul (isLegal_mul (isLegal_toAmb e1X) (isLegal_toAmb ΔX)) (isLegal_toAmb e1Y)) (isLegal_toAmb ΔY))
    (isLegal_pow (isLegal_toAmb QY) 4) hQY4

lemma specX_W_A_ne : specX ⟨W_A, W_A_isLegal⟩ ≠ 0 := by
  have hQY4 : specX ⟨QY_A ^ 4, isLegal_pow (isLegal_toAmb QY) 4⟩ ≠ 0 := by
    rw [specX_pow (isLegal_toAmb QY)]; exact pow_ne_zero 4 specX_QY_ne
  have hnum_l : IsLegal (e1X_A * ΔX_A * e1Y_A * ΔY_A) :=
    isLegal_mul (isLegal_mul (isLegal_mul (isLegal_toAmb e1X) (isLegal_toAmb ΔX)) (isLegal_toAmb e1Y)) (isLegal_toAmb ΔY)
  have hsub : (⟨W_A, W_A_isLegal⟩ : LegalAmb) =
      ⟨(e1X_A * ΔX_A * e1Y_A * ΔY_A) / QY_A ^ 4,
        isLegal_div hnum_l (isLegal_pow (isLegal_toAmb QY) 4) hQY4⟩ := Subtype.ext rfl
  rw [hsub, specX_div hnum_l (isLegal_pow (isLegal_toAmb QY) 4) hQY4]
  refine div_ne_zero ?_ hQY4
  rw [specX_mul (isLegal_mul (isLegal_mul (isLegal_toAmb e1X) (isLegal_toAmb ΔX)) (isLegal_toAmb e1Y)) (isLegal_toAmb ΔY),
      specX_mul (isLegal_mul (isLegal_toAmb e1X) (isLegal_toAmb ΔX)) (isLegal_toAmb e1Y),
      specX_mul (isLegal_toAmb e1X) (isLegal_toAmb ΔX)]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero specX_e1X_ne specX_ΔX_ne) specX_e1Y_ne) specX_ΔY_ne

lemma specX_Fx_amb_ne : specX ⟨eval5_amb (pderiv 3 F5), eval5_amb_isLegal _⟩ ≠ 0 := by
  have hp : pderiv (3 : Fin 5) F5 = 6 * X 0 * X 3 := by
    have hH : pderiv (3 : Fin 5) H0_5 = 0 := pderiv_3_poly4ToPoly5 H0_4
    simp only [F5, map_add, hH, add_zero, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul]
    simp; ring
  have hval : eval5_amb (pderiv 3 F5) = toAmb (6 * e1X * xNum6) / toAmb (QY ^ 2) := by
    rw [hp]
    simp only [eval5_amb, map_mul, map_ofNat, eval₂Hom_X', coord5,
      S_A, x_A, u3_A, Q_A, xNum6, e1X_A, e3X_A, QX_A, QY_A, map_add, map_sub, map_pow]
    have h1 : toAmb e1X ≠ 0 := e1X_A_ne
    have h3 : toAmb QY ≠ 0 := QY_A_ne
    field
  have hQY2 : residueMap (QY ^ 2) ≠ 0 := by rw [map_pow]; exact pow_ne_zero 2 residueMap_QY_ne
  change specXFun _ ≠ 0
  rw [specXFun_eq _ hQY2 hval]
  refine div_ne_zero ?_ hQY2
  simp only [map_mul, map_ofNat]
  exact mul_ne_zero (mul_ne_zero (by norm_num) residueMap_e1X_ne) residueMap_xNum6_ne

private lemma isLegal_invJac3 {a b c : Poly6}
    (hd : residueMap ((a - b) * (a - c) * (b - c)) ≠ 0) (i j : Fin 3) :
    IsLegal (invJac3 (toAmb a) (toAmb b) (toAmb c) i j) := by
  have hden : (toAmb a - toAmb b) * (toAmb a - toAmb c) * (toAmb b - toAmb c) =
      toAmb ((a - b) * (a - c) * (b - c)) := by simp
  have hden_ne : specX ⟨toAmb ((a - b) * (a - c) * (b - c)), isLegal_toAmb _⟩ ≠ 0 := by
    rw [specX_toAmb]; exact hd
  have ha := isLegal_toAmb a; have hb := isLegal_toAmb b; have hc := isLegal_toAmb c
  fin_cases i <;> fin_cases j <;> (
    dsimp only [invJac3]
    rw [hden]
    refine isLegal_div ?_ (isLegal_toAmb _) hden_ne
    repeat first | exact ha | exact hb | exact hc | apply isLegal_neg | apply isLegal_pow | apply isLegal_mul | apply isLegal_sub)

private lemma isLegal_nOuter6 {a1 a2 a3 b1 b2 b3 : AmbientField}
    (ha1 : IsLegal a1) (ha2 : IsLegal a2) (ha3 : IsLegal a3)
    (hb1 : IsLegal b1) (hb2 : IsLegal b2) (hb3 : IsLegal b3)
    (ha1ne : specX ⟨a1, ha1⟩ ≠ 0) (hb1ne : specX ⟨b1, hb1⟩ ≠ 0) (hb2ne : specX ⟨b2, hb2⟩ ≠ 0)
    (a b : Fin 6) : IsLegal (nOuter6 a1 a2 a3 b1 b2 b3 a b) := by
  have h2ne : specX ⟨(2 : AmbientField), isLegal_ofNat 2⟩ ≠ 0 := by rw [specX_ofNat]; norm_num
  have h2b2 : IsLegal (2 * b2) := isLegal_mul (isLegal_ofNat 2) hb2
  have h2b2ne : specX ⟨2 * b2, h2b2⟩ ≠ 0 := by
    rw [specX_mul (isLegal_ofNat 2) hb2]; exact mul_ne_zero h2ne hb2ne
  have h2a1 : IsLegal (2 * a1) := isLegal_mul (isLegal_ofNat 2) ha1
  have h2a1ne : specX ⟨2 * a1, h2a1⟩ ≠ 0 := by
    rw [specX_mul (isLegal_ofNat 2) ha1]; exact mul_ne_zero h2ne ha1ne
  have h2b1 : IsLegal (2 * b1) := isLegal_mul (isLegal_ofNat 2) hb1
  have h2b1ne : specX ⟨2 * b1, h2b1⟩ ≠ 0 := by
    rw [specX_mul (isLegal_ofNat 2) hb1]; exact mul_ne_zero h2ne hb1ne
  have h2a12 : IsLegal (2 * a1 ^ 2) := isLegal_mul (isLegal_ofNat 2) (isLegal_pow ha1 2)
  have h2a12ne : specX ⟨2 * a1 ^ 2, h2a12⟩ ≠ 0 := by
    rw [specX_mul (isLegal_ofNat 2) (isLegal_pow ha1 2), specX_pow ha1]
    exact mul_ne_zero h2ne (pow_ne_zero 2 ha1ne)
  have h2b12 : IsLegal (2 * b1 ^ 2) := isLegal_mul (isLegal_ofNat 2) (isLegal_pow hb1 2)
  have h2b12ne : specX ⟨2 * b1 ^ 2, h2b12⟩ ≠ 0 := by
    rw [specX_mul (isLegal_ofNat 2) (isLegal_pow hb1 2), specX_pow hb1]
    exact mul_ne_zero h2ne (pow_ne_zero 2 hb1ne)
  fin_cases a <;> fin_cases b <;> dsimp only [nOuter6]
  · exact isLegal_div ha1 h2b2 h2b2ne
  · exact isLegal_div hb2 h2a1 h2a1ne
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_div ha2 hb2 hb2ne
  · exact isLegal_zero
  · exact hb2
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_div (isLegal_mul (isLegal_ofNat 3) ha3) h2b2 h2b2ne
  · exact isLegal_div (isLegal_mul (isLegal_add (isLegal_mul (isLegal_neg (isLegal_ofNat 2)) (isLegal_pow ha1 3)) ha3) hb2) h2a12 h2a12ne
  · exact isLegal_mul (isLegal_mul (isLegal_ofNat 2) ha1) hb2
  · exact isLegal_zero
  · exact isLegal_mul ha1 hb2
  · exact isLegal_zero
  · exact isLegal_div hb1 h2b2 h2b2ne
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_div hb2 h2b1 h2b1ne
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_one
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_div (isLegal_mul (isLegal_ofNat 3) hb3) h2b2 h2b2ne
  · exact isLegal_zero
  · exact isLegal_zero
  · exact isLegal_div (isLegal_mul (isLegal_add (isLegal_mul (isLegal_neg (isLegal_ofNat 2)) (isLegal_pow hb1 3)) hb3) hb2) h2b12 h2b12ne
  · exact isLegal_zero
  · exact isLegal_mul hb1 hb2

lemma N_jac_isLegal (i j : Fin 6) : IsLegal (N_jac i j) := by
  have hN_in (a b : Fin 6) : IsLegal (N_inner a b) := by
    rw [N_inner, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    cases hfa : fin6Equiv a with
    | inl i1 =>
      cases hfb : fin6Equiv b with
      | inl j1 => rw [Matrix.fromBlocks_apply₁₁]; exact isLegal_invJac3 residueMap_ΔX_ne i1 j1
      | inr j2 => rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]; exact isLegal_zero
    | inr i2 =>
      cases hfb : fin6Equiv b with
      | inl j1 => rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact isLegal_zero
      | inr j2 => rw [Matrix.fromBlocks_apply₂₂]; exact isLegal_invJac3 residueMap_ΔY_ne i2 j2
  have hN_out (a b : Fin 6) : IsLegal (N_outer a b) :=
    isLegal_nOuter6 (isLegal_toAmb e1X) (isLegal_toAmb QX) (isLegal_toAmb e3X)
      (isLegal_toAmb e1Y) (isLegal_toAmb QY) (isLegal_toAmb e3Y)
      specX_e1X_ne specX_e1Y_ne specX_QY_ne a b
  rw [N_jac, Matrix.mul_apply]
  exact isLegal_sum Finset.univ _ fun k _ => isLegal_mul (hN_in i k) (hN_out k j)

lemma M_jac_det_isLegal : IsLegal M_jac.det := by
  rw [M_jac_det]
  have hQY5 : specX ⟨QY_A ^ 5, isLegal_pow (isLegal_toAmb QY) 5⟩ ≠ 0 := by
    rw [specX_pow (isLegal_toAmb QY)]; exact pow_ne_zero 5 specX_QY_ne
  exact isLegal_div
    (isLegal_mul (isLegal_mul (isLegal_neg (isLegal_ofNat 4)) (isLegal_toAmb ΔX)) (isLegal_toAmb ΔY))
    (isLegal_pow (isLegal_toAmb QY) 5) hQY5

lemma E_amb_isLegal (j : Fin 6) {z : AmbientField} (hz : IsLegal z) : IsLegal (E_amb j z) := by
  rw [E_amb_apply]
  exact isLegal_sum Finset.univ _ fun k _ => isLegal_mul (N_jac_isLegal k j) (D_amb_isLegal k hz)

-- Tangent derivations on AmbientField (annihilating sextic identically!) and descent to FunctionField
def T_amb (i : Fin 4) : Derivation ℤ AmbientField AmbientField :=
  E_amb (tanIdx i).succ -
    (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) • E_amb 4

lemma T_amb_isLegal (i : Fin 4) {z : AmbientField} (hz : IsLegal z) : IsLegal (T_amb i z) := by
  change IsLegal (E_amb (tanIdx i).succ z -
    (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) * E_amb 4 z)
  exact isLegal_sub (E_amb_isLegal _ hz)
    (isLegal_mul (isLegal_div (eval5_amb_isLegal _) (eval5_amb_isLegal _) specX_Fx_amb_ne)
      (E_amb_isLegal 4 hz))

lemma T_amb_sextic (i : Fin 4) : T_amb i (toAmb sextic) = 0 := by
  rw [F6_eq_QY3_F5]
  change E_amb (tanIdx i).succ (QY_A ^ 3 * eval5_amb F5) -
    (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) *
      E_amb (3 : Fin 5).succ (QY_A ^ 3 * eval5_amb F5) = 0
  have hQY0 (j : Fin 5) : E_amb j.succ QY_A = 0 := by
    change E_amb j.succ (coord6 0) = 0
    rw [E_amb_coord6, if_neg (Fin.succ_ne_zero j).symm]
  simp only [Derivation.leibniz, Derivation.leibniz_pow, hQY0, smul_eq_mul, nsmul_eq_mul,
    mul_zero, add_zero, E_amb_succ_eval5]
  have hFx : eval5_amb (pderiv 3 F5) ≠ 0 := by
    intro h0; apply specX_Fx_amb_ne
    have : (⟨eval5_amb (pderiv 3 F5), eval5_amb_isLegal _⟩ : LegalAmb) = 0 := Subtype.ext h0
    rw [this, map_zero]
  field

-- Descend T_amb i to a derivation on FunctionField
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra FunctionField
local instance : Algebra ℤ QuotientRing := Ring.toIntAlgebra QuotientRing

private def T_quot (i : Fin 4) : Derivation ℤ QuotientRing FunctionField :=
  let φ : Poly6 →+ FunctionField :=
    { toFun := fun p => specX ⟨T_amb i (toAmb p), T_amb_isLegal i (isLegal_toAmb p)⟩
      map_zero' := by
        have h : (⟨T_amb i (toAmb 0), T_amb_isLegal i (isLegal_toAmb 0)⟩ : LegalAmb) = 0 :=
          Subtype.ext (by simp)
        rw [h, map_zero]
      map_add' := fun p q => by
        rw [← map_add]; congr 1; apply Subtype.ext; simp [map_add] }
  have hker : ∀ p : Poly6, quotientMap p = 0 → φ p = 0 := by
    intro p hp
    rw [quotientMap_eq_zero_iff] at hp
    obtain ⟨q, rfl⟩ := hp
    change specX ⟨T_amb i (toAmb (sextic * q)), _⟩ = 0
    have hmul : (⟨T_amb i (toAmb (sextic * q)), T_amb_isLegal i (isLegal_toAmb _)⟩ : LegalAmb) =
        ⟨toAmb sextic, isLegal_toAmb sextic⟩ * ⟨T_amb i (toAmb q), T_amb_isLegal i (isLegal_toAmb q)⟩ := by
      apply Subtype.ext
      simp only [Subring.coe_mul, map_mul, Derivation.leibniz, T_amb_sextic, smul_eq_mul, mul_zero, add_zero]
    rw [hmul, map_mul, specX_toAmb, (residueMap_eq_zero_iff sextic).mpr dvd_rfl, zero_mul]
  let fQ : QuotientRing →+ FunctionField :=
    { toFun := fun x => φ (Classical.choose (quotientMap_surjective x))
      map_zero' := hker _ (by rw [Classical.choose_spec (quotientMap_surjective 0)])
      map_add' := fun x y => by
        let px := Classical.choose (quotientMap_surjective x)
        let py := Classical.choose (quotientMap_surjective y)
        let pxy := Classical.choose (quotientMap_surjective (x + y))
        have hdiff : quotientMap (pxy - (px + py)) = 0 := by
          rw [map_sub, map_add, Classical.choose_spec (quotientMap_surjective (x + y)),
            Classical.choose_spec (quotientMap_surjective x),
            Classical.choose_spec (quotientMap_surjective y), sub_self]
        have h0 := hker _ hdiff
        rw [map_sub, map_add] at h0
        exact sub_eq_zero.mp h0 }
  have hfQ (p : Poly6) : fQ (quotientMap p) = φ p := by
    let q := Classical.choose (quotientMap_surjective (quotientMap p))
    have hdiff : quotientMap (q - p) = 0 := by
      rw [map_sub, Classical.choose_spec (quotientMap_surjective (quotientMap p)), sub_self]
    have hfq : fQ (quotientMap p) = φ q := rfl
    rw [hfq]
    exact sub_eq_zero.mp (by simpa [map_sub] using hker _ hdiff)
  Derivation.mk' fQ.toIntLinearMap (by
    intro x y
    obtain ⟨p, rfl⟩ := quotientMap_surjective x
    obtain ⟨q, rfl⟩ := quotientMap_surjective y
    simp only [AddMonoidHom.coe_toIntLinearMap]
    rw [← map_mul, hfQ, hfQ, hfQ, Algebra.smul_def (R := QuotientRing) (A := FunctionField),
      Algebra.smul_def (R := QuotientRing) (A := FunctionField)]
    change specX ⟨T_amb i (toAmb (p * q)), _⟩ =
      residueMap p * specX ⟨T_amb i (toAmb q), _⟩ + residueMap q * specX ⟨T_amb i (toAmb p), _⟩
    rw [← specX_toAmb p (h := isLegal_toAmb p), ← specX_toAmb q (h := isLegal_toAmb q), ← map_mul, ← map_mul, ← map_add]
    refine congrArg specX (Subtype.ext ?_)
    simp only [Subring.coe_add, Subring.coe_mul, map_mul, Derivation.leibniz, smul_eq_mul])

def T_X (i : Fin 4) : Derivation ℤ FunctionField FunctionField :=
  HoldoutConstruction.FieldValuedFraction.extend (P := QuotientRing) (F := FunctionField) (T_quot i)

lemma T_X_residueMap (i : Fin 4) (p : Poly6) :
    T_X i (residueMap p) = specX ⟨T_amb i (toAmb p), T_amb_isLegal i (isLegal_toAmb p)⟩ := by
  change HoldoutConstruction.FieldValuedFraction.extend (T_quot i)
    (algebraMap QuotientRing FunctionField (quotientMap p)) = _
  rw [HoldoutConstruction.FieldValuedFraction.extend_map]
  change specX ⟨T_amb i (toAmb (Classical.choose (quotientMap_surjective (quotientMap p)))), _⟩ = _
  let q := Classical.choose (quotientMap_surjective (quotientMap p))
  have hdiff : sextic ∣ q - p := by
    rw [← quotientMap_eq_zero_iff, map_sub,
      Classical.choose_spec (quotientMap_surjective (quotientMap p)), sub_self]
  obtain ⟨r, hr⟩ := hdiff
  have hq : q = p + sextic * r := by linear_combination hr
  have hsub : (⟨T_amb i (toAmb q), T_amb_isLegal i (isLegal_toAmb q)⟩ : LegalAmb) =
      ⟨T_amb i (toAmb p), T_amb_isLegal i (isLegal_toAmb p)⟩ +
        ⟨toAmb sextic, isLegal_toAmb sextic⟩ * ⟨T_amb i (toAmb r), T_amb_isLegal i (isLegal_toAmb r)⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul]
    rw [hq, map_add, map_mul, map_add, Derivation.leibniz, T_amb_sextic]; simp
  rw [hsub, map_add, map_mul, specX_toAmb, (residueMap_eq_zero_iff sextic).mpr dvd_rfl, zero_mul, add_zero]

lemma T_X_specX (i : Fin 4) (z : LegalAmb) :
    T_X i (specX z) = specX ⟨T_amb i z.1, T_amb_isLegal i z.2⟩ := by
  obtain ⟨a, b, hb, hz⟩ := z.2
  have hspec : specX z = residueMap a / residueMap b := specXFun_eq z hb hz
  rw [hspec, Derivation.leibniz_div, T_X_residueMap, T_X_residueMap]
  have hbA := toAmb_ne_of_residue_ne hb
  have hnum : T_amb i z.1 =
      (T_amb i (toAmb a) * toAmb b - toAmb a * T_amb i (toAmb b)) / toAmb b ^ 2 := by
    rw [hz, Derivation.leibniz_div]; simp only [smul_eq_mul]; field
  have hb2 : specX ⟨toAmb b ^ 2, isLegal_pow (isLegal_toAmb b) 2⟩ ≠ 0 := by
    rw [specX_pow (isLegal_toAmb b), specX_toAmb]; exact pow_ne_zero 2 hb
  have hnum_l : IsLegal (T_amb i (toAmb a) * toAmb b - toAmb a * T_amb i (toAmb b)) :=
    isLegal_sub (isLegal_mul (T_amb_isLegal i (isLegal_toAmb a)) (isLegal_toAmb b))
      (isLegal_mul (isLegal_toAmb a) (T_amb_isLegal i (isLegal_toAmb b)))
  have hsub : (⟨T_amb i z.1, T_amb_isLegal i z.2⟩ : LegalAmb) =
      ⟨(T_amb i (toAmb a) * toAmb b - toAmb a * T_amb i (toAmb b)) / toAmb b ^ 2,
        isLegal_div hnum_l (isLegal_pow (isLegal_toAmb b) 2) hb2⟩ := Subtype.ext hnum
  rw [hsub, specX_div hnum_l (isLegal_pow (isLegal_toAmb b) 2) hb2,
    specX_sub (isLegal_mul (T_amb_isLegal i (isLegal_toAmb a)) (isLegal_toAmb b))
      (isLegal_mul (isLegal_toAmb a) (T_amb_isLegal i (isLegal_toAmb b))),
    specX_mul (T_amb_isLegal i (isLegal_toAmb a)) (isLegal_toAmb b),
    specX_mul (isLegal_toAmb a) (T_amb_isLegal i (isLegal_toAmb b)),
    specX_pow (isLegal_toAmb b), specX_toAmb, specX_toAmb]
  simp only [smul_eq_mul]
  field

-- Embedding K5 →+* FunctionField via coordinate independence
def coord4_X : Fin 4 → FunctionField :=
  fun i => specX ⟨coord6 (tanIdx i).succ, coord6_isLegal (tanIdx i).succ⟩

def eval4_X : Poly4 →+* FunctionField :=
  MvPolynomial.eval₂Hom (residueMap.comp MvPolynomial.C) coord4_X

lemma T_X_coord4 (i j : Fin 4) : T_X i (coord4_X j) = if j = i then 1 else 0 := by
  rw [coord4_X, T_X_specX]
  have hval : T_amb i (coord6 (tanIdx j).succ) = if j = i then 1 else 0 := by
    change E_amb (tanIdx i).succ (coord6 (tanIdx j).succ) -
      (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) *
        E_amb 4 (coord6 (tanIdx j).succ) = _
    have hj4 : (tanIdx j).succ ≠ 4 := by fin_cases j <;> decide
    rw [E_amb_coord6, E_amb_coord6, if_neg hj4, mul_zero, sub_zero]
    have hiff : (tanIdx j).succ = (tanIdx i).succ ↔ j = i := by
      fin_cases i <;> fin_cases j <;> simp [tanIdx]
    simp [hiff]
  by_cases hji : j = i
  · rw [if_pos hji] at hval ⊢
    have h1 : (⟨T_amb i (coord6 (tanIdx j).succ), T_amb_isLegal i (coord6_isLegal _)⟩ : LegalAmb) = 1 :=
      Subtype.ext hval
    rw [h1, map_one]
  · rw [if_neg hji] at hval ⊢
    have h0 : (⟨T_amb i (coord6 (tanIdx j).succ), T_amb_isLegal i (coord6_isLegal _)⟩ : LegalAmb) = 0 :=
      Subtype.ext hval
    rw [h0, map_zero]

lemma T_X_const (i : Fin 4) (c : ℂ) : T_X i (residueMap (C c)) = 0 := by
  rw [T_X_residueMap]
  have h0 : (⟨T_amb i (toAmb (C c)), T_amb_isLegal i (isLegal_toAmb (C c))⟩ : LegalAmb) = 0 := by
    apply Subtype.ext
    change E_amb (tanIdx i).succ (toAmb (C c)) -
      (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) * E_amb 4 (toAmb (C c)) = 0
    rw [E_amb_const, E_amb_const]; ring
  rw [h0, map_zero]

lemma eval4_X_injective : Function.Injective eval4_X :=
  HodgeComputer.Formal.ResidueTransport.injective_of_coordinate_derivations
    (residueMap.comp MvPolynomial.C) coord4_X T_X T_X_const T_X_coord4

lemma eval4_X_eq_specX (p : Poly4) :
    eval4_X p = specX ⟨eval5_amb (poly4ToPoly5 p), eval5_amb_isLegal _⟩ := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [eval4_X, eval₂Hom_C, RingHom.comp_apply, poly4ToPoly5]
    rw [← specX_toAmb (C c) (h := isLegal_toAmb (C c))]
    exact congrArg specX (Subtype.ext (by simp [eval5_amb]))
  | add p q hp hq =>
    rw [map_add, hp, hq, ← map_add]
    exact congrArg specX (Subtype.ext (by simp [map_add]))
  | mul_X p i hp =>
    rw [map_mul, hp]; simp only [eval4_X, eval₂Hom_X', coord4_X]
    rw [← map_mul]
    refine congrArg specX (Subtype.ext ?_)
    simp only [Subring.coe_mul, map_mul, poly4ToPoly5, eval₂Hom_X']
    congr 1; fin_cases i <;> simp [eval5_amb, coord5, coord6, tanIdx]

def k4ToX : K4 →+* FunctionField := IsFractionRing.lift eval4_X_injective

lemma k4ToX_poly4 (p : Poly4) : k4ToX (algebraMap Poly4 K4 p) = eval4_X p :=
  IsFractionRing.lift_algebraMap eval4_X_injective p

def x_X : FunctionField := specX ⟨x_A, coord6_isLegal 4⟩

lemma k5_embed_root : minPolyX.eval₂ k4ToX x_X = 0 := by
  rw [minPolyX_eq]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  rw [map_div₀, map_mul, map_ofNat, k4ToX_poly4, S_4, k4ToX_poly4, eval4_X_eq_specX, eval4_X_eq_specX]
  have hS_ne : specX ⟨S_A, coord6_isLegal 1⟩ ≠ 0 := by
    have h1 := eval4_X_injective.ne (show (X 0 : Poly4) ≠ 0 from fun h => by
      have := congrArg (MvPolynomial.eval ![1, 0, 0, 0]) h; simp at this)
    rw [map_zero, eval4_X_eq_specX] at h1
    simpa [poly4ToPoly5, eval5_amb, coord5, tanIdx] using h1
  have hF5_zero : specX ⟨eval5_amb F5, eval5_amb_isLegal F5⟩ = 0 := by
    have hQY3 : specX ⟨QY_A ^ 3, isLegal_pow (isLegal_toAmb QY) 3⟩ ≠ 0 := by
      rw [specX_pow (isLegal_toAmb QY), specX_toAmb]; exact pow_ne_zero 3 residueMap_QY_ne
    have hprod : specX ⟨QY_A ^ 3, isLegal_pow (isLegal_toAmb QY) 3⟩ *
        specX ⟨eval5_amb F5, eval5_amb_isLegal F5⟩ = 0 := by
      rw [← specX_mul (h := isLegal_mul (isLegal_pow (isLegal_toAmb QY) 3) (eval5_amb_isLegal F5))
        (isLegal_pow (isLegal_toAmb QY) 3) (eval5_amb_isLegal F5)]
      have heq : (⟨QY_A ^ 3 * eval5_amb F5, isLegal_mul (isLegal_pow (isLegal_toAmb QY) 3) (eval5_amb_isLegal F5)⟩ : LegalAmb) =
          ⟨toAmb sextic, isLegal_toAmb sextic⟩ := Subtype.ext F6_eq_QY3_F5.symm
      rw [heq, specX_toAmb, (residueMap_eq_zero_iff sextic).mpr dvd_rfl]
    exact (mul_eq_zero.mp hprod).resolve_left hQY3
  have hS_l : IsLegal S_A := coord6_isLegal 1
  have hx_l : IsLegal x_A := coord6_isLegal 4
  have hrel : 3 * specX ⟨S_A, hS_l⟩ * x_X ^ 2 +
      specX ⟨eval5_amb (poly4ToPoly5 radPoly4), eval5_amb_isLegal _⟩ = 0 := by
    rw [← hF5_zero, x_X]
    have h1 : (3 : FunctionField) * specX ⟨S_A, hS_l⟩ * specX ⟨x_A, hx_l⟩ ^ 2 +
        specX ⟨eval5_amb (poly4ToPoly5 radPoly4), eval5_amb_isLegal _⟩ =
        specX ⟨3 * S_A * x_A ^ 2 + eval5_amb (poly4ToPoly5 radPoly4),
          isLegal_add (isLegal_mul (isLegal_mul (isLegal_ofNat 3) hS_l)
            (isLegal_pow hx_l 2)) (eval5_amb_isLegal _)⟩ := by
      rw [specX_add (isLegal_mul (isLegal_mul (isLegal_ofNat 3) hS_l)
            (isLegal_pow hx_l 2)) (eval5_amb_isLegal _),
          specX_mul (isLegal_mul (isLegal_ofNat 3) hS_l) (isLegal_pow hx_l 2),
          specX_mul (isLegal_ofNat 3) hS_l,
          specX_ofNat 3, specX_pow hx_l]
    rw [h1]; refine congrArg specX (Subtype.ext ?_)
    simp only [F5, radPoly4, H0_5, map_add, map_mul, map_pow, map_ofNat, poly4ToPoly5,
      eval₂Hom_X', eval5_amb, coord5, tanIdx, Matrix.cons_val]
    ring
  have hS_eq : specX ⟨eval5_amb (poly4ToPoly5 (X 0)), eval5_amb_isLegal _⟩ =
      specX ⟨S_A, hS_l⟩ :=
    congrArg specX (Subtype.ext (by simp [poly4ToPoly5, eval5_amb, coord5, tanIdx]))
  rw [hS_eq]
  field_simp [hS_ne]; linear_combination hrel

def ι_K5 : K5 →+* FunctionField :=
  AdjoinRoot.lift k4ToX x_X k5_embed_root

private lemma ι_K5_k4ToK5 (a : K4) : ι_K5 (k4ToK5 a) = k4ToX a :=
  AdjoinRoot.lift_of k5_embed_root

lemma ι_K5_toK5 (p : Poly5) :
    ι_K5 (toK5 p) = specX ⟨eval5_amb p, eval5_amb_isLegal p⟩ := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have h1 : ι_K5 (toK5 (C c)) = residueMap (C c) := by
      have htc : toK5 (C c) = k4ToK5 (algebraMap Poly4 K4 (C c)) := by
        simp [toK5, poly4ToK5]
      rw [htc, ι_K5_k4ToK5, k4ToX_poly4]; simp [eval4_X]
    rw [h1, ← specX_toAmb (C c) (h := isLegal_toAmb (C c))]
    exact congrArg specX (Subtype.ext (by simp [eval5_amb]))
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, ← map_add]
    exact congrArg specX (Subtype.ext (by simp [map_add]))
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    have hXi : ι_K5 (toK5 (X i)) = specX ⟨eval5_amb (X i), eval5_amb_isLegal (X i)⟩ := by
      fin_cases i
      · have hX0 : toK5 (X (0 : Fin 5)) = k4ToK5 (algebraMap Poly4 K4 (X 0)) := by simp [toK5, S_K, S_4]
        change ι_K5 (toK5 (X 0)) = specX ⟨eval5_amb (X 0), _⟩
        rw [hX0, ι_K5_k4ToK5, k4ToX_poly4, eval4_X_eq_specX]
        exact congrArg specX (Subtype.ext (by simp [poly4ToPoly5, eval5_amb, coord5, tanIdx]))
      · have hX1 : toK5 (X (1 : Fin 5)) = k4ToK5 (algebraMap Poly4 K4 (X 1)) := by simp [toK5, Q_K, Q_4]
        change ι_K5 (toK5 (X 1)) = specX ⟨eval5_amb (X 1), _⟩
        rw [hX1, ι_K5_k4ToK5, k4ToX_poly4, eval4_X_eq_specX]
        exact congrArg specX (Subtype.ext (by simp [poly4ToPoly5, eval5_amb, coord5, tanIdx]))
      · have hX2 : toK5 (X (2 : Fin 5)) = k4ToK5 (algebraMap Poly4 K4 (X 2)) := by simp [toK5, T_K, T_4]
        change ι_K5 (toK5 (X 2)) = specX ⟨eval5_amb (X 2), _⟩
        rw [hX2, ι_K5_k4ToK5, k4ToX_poly4, eval4_X_eq_specX]
        exact congrArg specX (Subtype.ext (by simp [poly4ToPoly5, eval5_amb, coord5, tanIdx]))
      · have hX3 : toK5 (X (3 : Fin 5)) = x_K := by simp [toK5]
        change ι_K5 (toK5 (X 3)) = specX ⟨eval5_amb (X 3), _⟩
        rw [hX3, ι_K5, x_K, AdjoinRoot.lift_root, x_X]
        exact congrArg specX (Subtype.ext (by simp [eval5_amb, coord5]))
      · have hX4 : toK5 (X (4 : Fin 5)) = k4ToK5 (algebraMap Poly4 K4 (X 3)) := by simp [toK5, y_K, y_4]
        change ι_K5 (toK5 (X 4)) = specX ⟨eval5_amb (X 4), _⟩
        rw [hX4, ι_K5_k4ToK5, k4ToX_poly4, eval4_X_eq_specX]
        exact congrArg specX (Subtype.ext (by simp [poly4ToPoly5, eval5_amb, coord5, tanIdx]))
    rw [hXi, ← map_mul]
    exact congrArg specX (Subtype.ext (by simp [map_mul]))

-- Main theorem: ANY K5 residue divergence solution lifts via 6×6 ambient Piola to HasCertificate!
set_option maxHeartbeats 2000000 in
theorem certificate_of_K5_pde (w : Fin 4 → K5) (heq : srcX + resDivW w = 0) :
    HodgeComputer.HasCertificate (n := HodgeComputer.SymmetricSexticResidual.n) HodgeComputer.SymmetricSexticResidual.F HodgeComputer.SymmetricSexticResidual.A HodgeComputer.SymmetricSexticResidual.d HodgeComputer.SymmetricSexticResidual.q := by
  obtain ⟨d, hd0, n, hn⟩ := exists_poly4_denom w
  have hd_X : specX ⟨eval5_amb (poly4ToPoly5 d), eval5_amb_isLegal _⟩ ≠ 0 := by
    rw [← eval4_X_eq_specX]; exact (map_ne_zero_iff eval4_X eval4_X_injective).mpr hd0
  have hd_A : eval5_amb (poly4ToPoly5 d) ≠ 0 := by
    intro h0; apply hd_X
    have : (⟨eval5_amb (poly4ToPoly5 d), eval5_amb_isLegal _⟩ : LegalAmb) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hFx_X := specX_Fx_amb_ne
  have hFx_A : eval5_amb (pderiv 3 F5) ≠ 0 := by
    intro h0; apply hFx_X
    have : (⟨eval5_amb (pderiv 3 F5), eval5_amb_isLegal _⟩ : LegalAmb) = 0 := Subtype.ext h0
    rw [this, map_zero]
  -- Define 5-variable ambient vector v5 (with v5(x) solving the exact normal identity!)
  let v5_tan : Fin 4 → AmbientField :=
    fun i => eval5_amb (n i) / (eval5_amb (poly4ToPoly5 d) * W_A)
  let v5_x : AmbientField :=
    (eval5_amb MA_5 / W_A - ∑ i : Fin 4, v5_tan i * eval5_amb (pderiv (tanIdx i) F5)) /
      eval5_amb (pderiv 3 F5)
  let v5 : Fin 5 → AmbientField :=
    ![v5_tan 0, v5_tan 1, v5_tan 2, v5_x, v5_tan 3]
  -- Append 0 in the passive QY-slot and scale by -(1/4)*QY^2
  let v_new : Fin 6 → AmbientField :=
    Fin.cases 0 (fun j => -(1 / 4 : AmbientField) * QY_A ^ 2 * v5 j)
  -- Pull back to physical (X0..Y2) coordinates via 6×6 ambient Piola!
  let v_phys : Fin 6 → AmbientField :=
    fun k => M_jac.det * (N_jac.mulVec v_new) k
  -- 1. Check exact pushforward M * (v_phys / det M) = v_new
  have hpush (j : Fin 6) : ∑ k : Fin 6, (v_phys k / M_jac.det) * M_jac j k = v_new j := by
    have hv (k : Fin 6) : v_phys k / M_jac.det = (N_jac.mulVec v_new) k := by
      dsimp only [v_phys]; field_simp [M_jac_det_ne]
    simp_rw [hv]
    have hm := congrFun (Matrix.mulVec_mulVec v_new M_jac N_jac) j
    rw [M_mul_N, Matrix.one_mulVec] at hm
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using hm
  -- 2. Exact ambient normal identity: ∑ k, v_phys k * D_amb k sextic = toAmb source!
  have hnorm_v5 : ∑ j : Fin 5, v5 j * eval5_amb (pderiv j F5) = eval5_amb MA_5 / W_A := by
    rw [Fin.sum_univ_five]
    simp only [v5, v5_x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.sum_univ_four, tanIdx]
    field
  have hnorm_phys : ∑ k : Fin 6, v_phys k * D_amb k (toAmb sextic) = toAmb source := by
    have hpc := HodgeComputer.Formal.HoldoutCover.piola_contraction D_amb E_amb M_jac N_jac N_mul_M
      E_amb_apply v_phys (toAmb sextic)
    simp_rw [hpush] at hpc
    have hLHS : ∑ j : Fin 6, v_new j * E_amb j (toAmb sextic) =
        -(1 / 4 : AmbientField) * QY_A ^ 5 * (eval5_amb MA_5 / W_A) := by
      rw [Fin.sum_univ_succ]
      simp only [v_new, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]
      have hEj (j : Fin 5) : E_amb j.succ (toAmb sextic) = QY_A ^ 3 * eval5_amb (pderiv j F5) := by
        rw [F6_eq_QY3_F5, Derivation.leibniz, Derivation.leibniz_pow]
        have hQY0 : E_amb j.succ QY_A = 0 := by
          change E_amb j.succ (coord6 0) = 0; rw [E_amb_coord6, if_neg (Fin.succ_ne_zero j).symm]
        rw [hQY0, E_amb_succ_eval5]; simp
      simp_rw [hEj]
      calc
        ∑ j : Fin 5, -(1 / 4 : AmbientField) * QY_A ^ 2 * v5 j * (QY_A ^ 3 * eval5_amb (pderiv j F5))
            = -(1 / 4 : AmbientField) * QY_A ^ 5 * ∑ j : Fin 5, v5 j * eval5_amb (pderiv j F5) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ = _ := by rw [hnorm_v5]
    rw [hLHS] at hpc
    have h1 := (eq_div_iff M_jac_det_ne).mp hpc
    rw [← h1, M_jac_det, MA_over_W]
    have h3 := QY_A_ne; have h4 := ΔX_A_ne; have h5 := ΔY_A_ne
    field
  -- 3. Ambient Piola divergence identity: ∑ k, D_amb k (v_phys k) = -(1/4) * QY^2 * det M * div5(v5)
  have hdiv_phys : ∑ k : Fin 6, D_amb k (v_phys k) =
      -(1 / 4 : AmbientField) * QY_A ^ 2 * M_jac.det * ∑ j : Fin 5, E_amb j.succ (v5 j) := by
    have hpd := HodgeComputer.Formal.HoldoutCover.piola_divergence D_amb E_amb M_jac N_jac
      M_jac_det_ne N_mul_M E_amb_apply M_jac_mixed v_phys
    have hpush_fn : (fun j => ∑ k : Fin 6, (v_phys k / M_jac.det) * M_jac j k) = v_new := funext hpush
    rw [hpush_fn] at hpd
    have h1 := (eq_div_iff M_jac_det_ne).mp hpd
    have hdiv_new : HoldoutConstruction.fieldDivergence E_amb v_new =
        -(1 / 4 : AmbientField) * QY_A ^ 2 * ∑ j : Fin 5, E_amb j.succ (v5 j) := by
      rw [HoldoutConstruction.fieldDivergence, Fin.sum_univ_succ]
      simp only [v_new, Fin.cases_zero, Fin.cases_succ, map_zero, zero_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      have hQY0 : E_amb j.succ QY_A = 0 := by
        change E_amb j.succ (coord6 0) = 0; rw [E_amb_coord6, if_neg (Fin.succ_ne_zero j).symm]
      have hC0 : E_amb j.succ (-(1 / 4 : AmbientField)) = 0 := by
        have h4 : (-(1 / 4 : AmbientField)) = toAmb (C (-(1 / 4 : ℂ))) := by
          have h4ne : (4 : AmbientField) ≠ 0 := by norm_num
          have hmul : toAmb (C (-(1 / 4 : ℂ))) * 4 = -1 := by
            rw [← map_ofNat toAmb 4, ← map_mul]
            have hC : C (σ := Fin 6) (-(1 / 4 : ℂ)) * 4 = -1 := by
              rw [← map_ofNat C 4, ← map_mul]; norm_num
            rw [hC, map_neg, map_one]
          field_simp [h4ne]; linear_combination -hmul
        rw [h4]; exact E_amb_const j.succ _
      rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hQY0, hC0]
      simp [smul_eq_mul]
    change HoldoutConstruction.fieldDivergence D_amb v_phys = _
    rw [← h1, hdiv_new]; ring
  -- 4. Legality of v5, v_new, v_phys!
  have hdW_legal : IsLegal (eval5_amb (poly4ToPoly5 d) * W_A) :=
    isLegal_mul (eval5_amb_isLegal _) W_A_isLegal
  have hdW_ne : specX ⟨eval5_amb (poly4ToPoly5 d) * W_A, hdW_legal⟩ ≠ 0 := by
    rw [specX_mul (eval5_amb_isLegal _) W_A_isLegal]; exact mul_ne_zero hd_X specX_W_A_ne
  have hv5_tan_legal (i : Fin 4) : IsLegal (v5_tan i) :=
    isLegal_div (eval5_amb_isLegal _) hdW_legal hdW_ne
  have hv5_x_legal : IsLegal v5_x :=
    isLegal_div
      (isLegal_sub (isLegal_div (eval5_amb_isLegal _) W_A_isLegal specX_W_A_ne)
        (isLegal_sum Finset.univ _ fun i _ => isLegal_mul (hv5_tan_legal i) (eval5_amb_isLegal _)))
      (eval5_amb_isLegal _) hFx_X
  have hv5_legal (j : Fin 5) : IsLegal (v5 j) := by
    fin_cases j
    · exact hv5_tan_legal 0
    · exact hv5_tan_legal 1
    · exact hv5_tan_legal 2
    · exact hv5_x_legal
    · exact hv5_tan_legal 3
  have hneg4_legal : IsLegal (-(1 / 4 : AmbientField)) := by
    have h4 : (-(1 / 4 : AmbientField)) = toAmb (C (-(1 / 4 : ℂ))) := by
      have h4ne : (4 : AmbientField) ≠ 0 := by norm_num
      have hmul : toAmb (C (-(1 / 4 : ℂ))) * 4 = -1 := by
        rw [← map_ofNat toAmb 4, ← map_mul]
        have hC : C (σ := Fin 6) (-(1 / 4 : ℂ)) * 4 = -1 := by
          rw [← map_ofNat C 4, ← map_mul]; norm_num
        rw [hC, map_neg, map_one]
      field_simp [h4ne]; linear_combination -hmul
    rw [h4]; exact isLegal_toAmb _
  have hv_new_legal (j : Fin 6) : IsLegal (v_new j) := by
    refine Fin.cases isLegal_zero (fun j => ?_) j
    exact isLegal_mul (isLegal_mul hneg4_legal (isLegal_pow (isLegal_toAmb QY) 2)) (hv5_legal j)
  have hv_phys_legal (k : Fin 6) : IsLegal (v_phys k) :=
    isLegal_mul M_jac_det_isLegal
      (isLegal_sum Finset.univ _ fun j _ => isLegal_mul (N_jac_isLegal k j) (hv_new_legal j))
  -- 5. Prove specX (∑ j, E_amb j.succ (v5 j)) = 0 via clean per-index T_amb factorization!
  have hdiv5_zero : specX ⟨∑ j : Fin 5, E_amb j.succ (v5 j),
      isLegal_sum Finset.univ _ fun j _ => E_amb_isLegal j.succ (hv5_legal j)⟩ = 0 := by
    have hW2_A : eval5_amb W2_5 ≠ 0 := by rw [← W_A_sq]; exact pow_ne_zero 2 W_A_ne
    have hW2_X : specX ⟨eval5_amb W2_5, eval5_amb_isLegal W2_5⟩ ≠ 0 := by
      rw [← ι_K5_toK5]; exact (map_ne_zero_iff ι_K5 ι_K5.injective).mpr W2_K_ne_zero
    have h2W2_X : specX ⟨2 * eval5_amb W2_5, isLegal_mul (isLegal_ofNat 2) (eval5_amb_isLegal W2_5)⟩ ≠ 0 := by
      rw [specX_mul (isLegal_ofNat 2) (eval5_amb_isLegal W2_5), specX_ofNat 2]
      exact mul_ne_zero (by norm_num) hW2_X
    have hcomm (i : Fin 4) : pderiv 3 (pderiv (tanIdx i) F5) = pderiv (tanIdx i) (pderiv 3 F5) := by
      have hp3 : pderiv (3 : Fin 5) F5 = 6 * X 0 * X 3 := by
        have hH : pderiv (3 : Fin 5) H0_5 = 0 := pderiv_3_poly4ToPoly5 H0_4
        simp only [F5, map_add, hH, add_zero, Derivation.leibniz, Derivation.leibniz_pow,
          pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul]; simp; ring
      have hpt : pderiv (tanIdx i) F5 =
          3 * pderiv (tanIdx i) (X 0) * X 3 ^ 2 +
          3 * pderiv (tanIdx i) (X 2) * X 4 ^ 2 +
          6 * X 2 * X 4 * pderiv (tanIdx i) (X 4) +
          poly4ToPoly5 (pderiv i H0_4) := by
        simp only [F5, H0_5, map_add, Derivation.leibniz, Derivation.leibniz_pow,
          pderiv_ofNat, pderiv_poly4ToPoly5, pderiv_X, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
        fin_cases i <;> simp [tanIdx] <;> ring
      rw [hp3, hpt]
      have hH3 : pderiv (3 : Fin 5) (poly4ToPoly5 (pderiv i H0_4)) = 0 := pderiv_3_poly4ToPoly5 _
      fin_cases i <;>
        simp only [tanIdx, map_add, hH3, add_zero, Derivation.leibniz,
          Derivation.leibniz_pow, pderiv_ofNat, pderiv_X, smul_eq_mul, nsmul_eq_mul] <;>
        simp; ring
    have hT_eval5 (i : Fin 4) (p : Poly5) :
        T_amb i (eval5_amb p) = eval5_amb (pderiv (tanIdx i) p) -
          (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) * eval5_amb (pderiv 3 p) := by
      change E_amb (tanIdx i).succ (eval5_amb p) -
        (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) * E_amb (3 : Fin 5).succ (eval5_amb p) = _
      rw [E_amb_succ_eval5, E_amb_succ_eval5]
    have hspec_T_eval5 (i : Fin 4) (p : Poly5) :
        specX ⟨T_amb i (eval5_amb p), T_amb_isLegal i (eval5_amb_isLegal p)⟩ = ι_K5 (δ i (toK5 p)) := by
      have hl : (⟨T_amb i (eval5_amb p), T_amb_isLegal i (eval5_amb_isLegal p)⟩ : LegalAmb) =
          ⟨eval5_amb (pderiv (tanIdx i) p), eval5_amb_isLegal _⟩ -
            ⟨eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5),
              isLegal_div (eval5_amb_isLegal _) (eval5_amb_isLegal _) hFx_X⟩ *
            ⟨eval5_amb (pderiv 3 p), eval5_amb_isLegal _⟩ := Subtype.ext (hT_eval5 i p)
      rw [hl, map_sub, map_mul, specX_div (eval5_amb_isLegal _) (eval5_amb_isLegal _) hFx_X, δ_toK5]
      simp only [map_sub, map_mul, map_div₀, ι_K5_toK5, Fx_K]
    have hT_W (i : Fin 4) :
        T_amb i W_A = W_A * T_amb i (eval5_amb W2_5) / (2 * eval5_amb W2_5) := by
      have h := congrArg (T_amb i) W_A_sq
      rw [Derivation.leibniz_pow] at h
      simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at h
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one] at h
      have h2W : (2 * eval5_amb W2_5 : AmbientField) ≠ 0 := mul_ne_zero (by norm_num) hW2_A
      apply (eq_div_iff h2W).mpr
      rw [show 2 * eval5_amb W2_5 = 2 * W_A ^ 2 from congrArg (2 * ·) W_A_sq.symm]
      linear_combination W_A * h
    let wi_amb : Fin 4 → AmbientField := fun i => eval5_amb (n i) / eval5_amb (poly4ToPoly5 d)
    have hwi_legal (i : Fin 4) : IsLegal (wi_amb i) :=
      isLegal_div (eval5_amb_isLegal _) (eval5_amb_isLegal _) hd_X
    have hspec_wi (i : Fin 4) : specX ⟨wi_amb i, hwi_legal i⟩ = ι_K5 (w i) := by
      have hwi_K : w i = toK5 (n i) / toK5 (poly4ToPoly5 d) := by
        rw [toK5_poly4, hn i]; field_simp [poly4ToK5_ne_zero hd0]
      rw [hwi_K, map_div₀, ι_K5_toK5, ι_K5_toK5]
      exact specX_div (eval5_amb_isLegal _) (eval5_amb_isLegal _) hd_X
    have hspec_T_wi (i : Fin 4) :
        specX ⟨T_amb i (wi_amb i), T_amb_isLegal i (hwi_legal i)⟩ = ι_K5 (δ i (w i)) := by
      have hTX : specX ⟨T_amb i (wi_amb i), T_amb_isLegal i (hwi_legal i)⟩ =
          T_X i (specX ⟨wi_amb i, hwi_legal i⟩) := (T_X_specX i ⟨wi_amb i, hwi_legal i⟩).symm
      rw [hTX, hspec_wi]
      have hwi_K : w i = toK5 (n i) / toK5 (poly4ToPoly5 d) := by
        rw [toK5_poly4, hn i]; field_simp [poly4ToK5_ne_zero hd0]
      have hdK : toK5 (poly4ToPoly5 d) ≠ 0 := by rw [toK5_poly4]; exact poly4ToK5_ne_zero hd0
      have hdF : ι_K5 (toK5 (poly4ToPoly5 d)) ≠ 0 := (map_ne_zero_iff ι_K5 ι_K5.injective).mpr hdK
      have hδ_div : δ i (toK5 (n i) / toK5 (poly4ToPoly5 d)) =
          (toK5 (poly4ToPoly5 d) * δ i (toK5 (n i)) - toK5 (n i) * δ i (toK5 (poly4ToPoly5 d))) /
            toK5 (poly4ToPoly5 d) ^ 2 := by
        let : Algebra ℤ K5 := Ring.toIntAlgebra K5
        have h := congrArg (δ i) (div_mul_cancel₀ (toK5 (n i)) hdK)
        rw [(δ i).leibniz] at h; simp only [smul_eq_mul] at h
        have h2 := congrArg (toK5 (poly4ToPoly5 d) * ·) h
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hdK] at h2
        rw [eq_div_iff (pow_ne_zero 2 hdK)]; linear_combination h2
      have hT_div : T_X i (ι_K5 (toK5 (n i)) / ι_K5 (toK5 (poly4ToPoly5 d))) =
          (ι_K5 (toK5 (poly4ToPoly5 d)) * T_X i (ι_K5 (toK5 (n i))) -
            ι_K5 (toK5 (n i)) * T_X i (ι_K5 (toK5 (poly4ToPoly5 d)))) /
            ι_K5 (toK5 (poly4ToPoly5 d)) ^ 2 := by
        have h := congrArg (T_X i) (div_mul_cancel₀ (ι_K5 (toK5 (n i))) hdF)
        rw [(T_X i).leibniz] at h; simp only [smul_eq_mul] at h
        have h2 := congrArg (ι_K5 (toK5 (poly4ToPoly5 d)) * ·) h
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hdF] at h2
        rw [eq_div_iff (pow_ne_zero 2 hdF)]; linear_combination h2
      rw [hwi_K, map_div₀, hT_div, hδ_div]
      simp only [map_div₀, map_sub, map_mul, map_pow]
      have hT_ni : T_X i (ι_K5 (toK5 (n i))) = ι_K5 (δ i (toK5 (n i))) := by
        rw [ι_K5_toK5, T_X_specX, hspec_T_eval5]
      have hT_d : T_X i (ι_K5 (toK5 (poly4ToPoly5 d))) = ι_K5 (δ i (toK5 (poly4ToPoly5 d))) := by
        rw [ι_K5_toK5, T_X_specX, hspec_T_eval5]
      rw [hT_ni, hT_d]
    -- Split ambient divergence cleanly into source term + sum of 4 tangent terms
    let src_amb : AmbientField :=
      ((eval5_amb (pderiv 3 MA_5) - eval5_amb MA_5 * eval5_amb (pderiv 3 W2_5) / (2 * eval5_amb W2_5)) *
          eval5_amb (pderiv 3 F5) -
        eval5_amb MA_5 * eval5_amb (pderiv 3 (pderiv 3 F5))) / eval5_amb (pderiv 3 F5) ^ 2
    let tan_amb : Fin 4 → AmbientField := fun i =>
      T_amb i (wi_amb i) - wi_amb i * T_amb i (eval5_amb (pderiv 3 F5)) / eval5_amb (pderiv 3 F5) -
        wi_amb i * T_amb i (eval5_amb W2_5) / (2 * eval5_amb W2_5)
    have hdiv5_eq : ∑ j : Fin 5, E_amb j.succ (v5 j) =
        (src_amb + ∑ i : Fin 4, tan_amb i) / W_A := by
      have hv5x_split : v5_x = eval5_amb MA_5 / (W_A * eval5_amb (pderiv 3 F5)) -
          ∑ i : Fin 4, v5_tan i * eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5) := by
        dsimp only [v5_x]
        rw [sub_div, Finset.sum_div, div_div]
      have hsum_split : ∑ j : Fin 5, E_amb j.succ (v5 j) =
          E_amb 4 (eval5_amb MA_5 / (W_A * eval5_amb (pderiv 3 F5))) +
          ∑ i : Fin 4, (E_amb (tanIdx i).succ (v5_tan i) -
            E_amb 4 (v5_tan i * eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5))) := by
        rw [Fin.sum_univ_five, Fin.sum_univ_four]
        simp only [v5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        rw [hv5x_split, map_sub, map_sum, Fin.sum_univ_four]
        simp only [show (3 : Fin 5).succ = 4 from rfl, tanIdx,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        ring
      have hsrc_term : E_amb 4 (eval5_amb MA_5 / (W_A * eval5_amb (pderiv 3 F5))) = src_amb / W_A := by
        dsimp only [src_amb]
        rw [show (4 : Fin 6) = (3 : Fin 5).succ from rfl,
          Derivation.leibniz_div, Derivation.leibniz, E_amb_succ_eval5, E_amb_succ_eval5, E_amb_succ_W]
        simp only [smul_eq_mul]
        have hW := W_A_ne
        generalize eval5_amb MA_5 = ma; generalize eval5_amb (pderiv 3 MA_5) = d3ma
        generalize eval5_amb (pderiv 3 F5) = fx at hFx_A ⊢
        generalize eval5_amb (pderiv 3 (pderiv 3 F5)) = fxx
        generalize eval5_amb W2_5 = w2 at hW2_A ⊢; generalize eval5_amb (pderiv 3 W2_5) = d3w2
        generalize W_A = wa at hW ⊢
        field
      have htan_term (i : Fin 4) :
          E_amb (tanIdx i).succ (v5_tan i) -
            E_amb 4 (v5_tan i * eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) =
          tan_amb i / W_A := by
        have hstep1 : E_amb (tanIdx i).succ (v5_tan i) -
            E_amb 4 (v5_tan i * eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) =
            T_amb i (v5_tan i) - v5_tan i * T_amb i (eval5_amb (pderiv 3 F5)) / eval5_amb (pderiv 3 F5) := by
          have hE4 : E_amb 4 (v5_tan i * eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) =
              (eval5_amb (pderiv 3 F5) * (E_amb 4 (v5_tan i) * eval5_amb (pderiv (tanIdx i) F5) +
                v5_tan i * eval5_amb (pderiv (tanIdx i) (pderiv 3 F5))) -
                v5_tan i * eval5_amb (pderiv (tanIdx i) F5) * eval5_amb (pderiv 3 (pderiv 3 F5))) /
                eval5_amb (pderiv 3 F5) ^ 2 := by
            rw [show (4 : Fin 6) = (3 : Fin 5).succ from rfl,
              Derivation.leibniz_div, Derivation.leibniz, E_amb_succ_eval5, E_amb_succ_eval5, hcomm i]
            simp only [smul_eq_mul]; field
          rw [hE4, hT_eval5]
          change E_amb (tanIdx i).succ (v5_tan i) - _ =
            (E_amb (tanIdx i).succ (v5_tan i) -
              (eval5_amb (pderiv (tanIdx i) F5) / eval5_amb (pderiv 3 F5)) * E_amb 4 (v5_tan i)) - _
          generalize v5_tan i = u; generalize E_amb (tanIdx i).succ (v5_tan i) = dui
          generalize E_amb 4 (v5_tan i) = du3
          generalize eval5_amb (pderiv (tanIdx i) F5) = fi
          generalize eval5_amb (pderiv 3 F5) = fx at hFx_A ⊢
          generalize eval5_amb (pderiv (tanIdx i) (pderiv 3 F5)) = fix
          generalize eval5_amb (pderiv 3 (pderiv 3 F5)) = fxx
          field
        have hv_eq : v5_tan i = wi_amb i / W_A := by
          dsimp only [v5_tan, wi_amb]; rw [div_div]
        rw [hstep1, hv_eq, Derivation.leibniz_div, hT_W]
        dsimp only [tan_amb]
        simp only [smul_eq_mul]
        have hW := W_A_ne
        generalize wi_amb i = wi; generalize T_amb i (wi_amb i) = twi
        generalize T_amb i (eval5_amb (pderiv 3 F5)) = tfx
        generalize T_amb i (eval5_amb W2_5) = tw2
        generalize eval5_amb (pderiv 3 F5) = fx at hFx_A ⊢
        generalize eval5_amb W2_5 = w2 at hW2_A ⊢
        generalize W_A = wa at hW ⊢
        field
      rw [hsum_split, hsrc_term, Finset.sum_congr rfl fun i _ => htan_term i, add_div, Finset.sum_div]
    -- Map through specX!
    have hFx2_X : specX ⟨eval5_amb (pderiv 3 F5) ^ 2, isLegal_pow (eval5_amb_isLegal _) 2⟩ ≠ 0 := by
      rw [specX_pow (eval5_amb_isLegal _)]; exact pow_ne_zero 2 hFx_X
    have hsrc_legal : IsLegal src_amb :=
      isLegal_div
        (isLegal_sub
          (isLegal_mul
            (isLegal_sub (eval5_amb_isLegal _)
              (isLegal_div (isLegal_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _))
                (isLegal_mul (isLegal_ofNat 2) (eval5_amb_isLegal _)) h2W2_X))
            (eval5_amb_isLegal _))
          (isLegal_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _)))
        (isLegal_pow (eval5_amb_isLegal _) 2) hFx2_X
    have htan_legal (i : Fin 4) : IsLegal (tan_amb i) :=
      isLegal_sub
        (isLegal_sub (T_amb_isLegal i (hwi_legal i))
          (isLegal_div (isLegal_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)))
            (eval5_amb_isLegal _) hFx_X))
        (isLegal_div (isLegal_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)))
          (isLegal_mul (isLegal_ofNat 2) (eval5_amb_isLegal _)) h2W2_X)
    have hnum_l : IsLegal (src_amb + ∑ i : Fin 4, tan_amb i) :=
      isLegal_add hsrc_legal (isLegal_sum Finset.univ _ fun i _ => htan_legal i)
    have hsub : (⟨∑ j : Fin 5, E_amb j.succ (v5 j),
        isLegal_sum Finset.univ _ fun j _ => E_amb_isLegal j.succ (hv5_legal j)⟩ : LegalAmb) =
        ⟨(src_amb + ∑ i : Fin 4, tan_amb i) / W_A,
          isLegal_div hnum_l W_A_isLegal specX_W_A_ne⟩ := Subtype.ext hdiv5_eq
    rw [hsub, specX_div hnum_l W_A_isLegal specX_W_A_ne]
    have hnum_zero : specX ⟨src_amb + ∑ i : Fin 4, tan_amb i, hnum_l⟩ = 0 := by
      have hsrc_spec : specX ⟨src_amb, hsrc_legal⟩ = ι_K5 srcX := by
        dsimp only [src_amb, srcX, MA_K, W2_K, Fx_K]
        have hl_rat : IsLegal (eval5_amb MA_5 * eval5_amb (pderiv 3 W2_5) / (2 * eval5_amb W2_5)) :=
          isLegal_div (isLegal_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _))
            (isLegal_mul (isLegal_ofNat 2) (eval5_amb_isLegal _)) h2W2_X
        have hl_inner : IsLegal (eval5_amb (pderiv 3 MA_5) - eval5_amb MA_5 * eval5_amb (pderiv 3 W2_5) / (2 * eval5_amb W2_5)) :=
          isLegal_sub (eval5_amb_isLegal _) hl_rat
        have hl_prod : IsLegal ((eval5_amb (pderiv 3 MA_5) - eval5_amb MA_5 * eval5_amb (pderiv 3 W2_5) / (2 * eval5_amb W2_5)) *
            eval5_amb (pderiv 3 F5)) := isLegal_mul hl_inner (eval5_amb_isLegal _)
        have hl_top : IsLegal ((eval5_amb (pderiv 3 MA_5) - eval5_amb MA_5 * eval5_amb (pderiv 3 W2_5) / (2 * eval5_amb W2_5)) *
            eval5_amb (pderiv 3 F5) - eval5_amb MA_5 * eval5_amb (pderiv 3 (pderiv 3 F5))) :=
          isLegal_sub hl_prod (isLegal_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _))
        rw [specX_div hl_top (isLegal_pow (eval5_amb_isLegal _) 2) hFx2_X,
            specX_pow (eval5_amb_isLegal _),
            specX_sub hl_prod (isLegal_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _)),
            specX_mul hl_inner (eval5_amb_isLegal _),
            specX_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _),
            specX_sub (eval5_amb_isLegal _) hl_rat,
            specX_div (isLegal_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _))
              (isLegal_mul (isLegal_ofNat 2) (eval5_amb_isLegal _)) h2W2_X,
            specX_mul (eval5_amb_isLegal _) (eval5_amb_isLegal _),
            specX_mul (isLegal_ofNat 2) (eval5_amb_isLegal _),
            specX_ofNat 2]
        simp only [ι_K5_toK5, map_div₀, map_sub, map_mul, map_pow, map_ofNat]
      have htan_spec (i : Fin 4) : specX ⟨tan_amb i, htan_legal i⟩ =
          ι_K5 (δ i (w i) - w i * δ i Fx_K / Fx_K - w i * δ i W2_K / (2 * W2_K)) := by
        dsimp only [tan_amb, Fx_K, W2_K]
        have hl_a : IsLegal (wi_amb i * T_amb i (eval5_amb (pderiv 3 F5)) / eval5_amb (pderiv 3 F5)) :=
          isLegal_div (isLegal_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)))
            (eval5_amb_isLegal _) hFx_X
        have hl_b : IsLegal (wi_amb i * T_amb i (eval5_amb W2_5) / (2 * eval5_amb W2_5)) :=
          isLegal_div (isLegal_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)))
            (isLegal_mul (isLegal_ofNat 2) (eval5_amb_isLegal _)) h2W2_X
        have hl_ab : IsLegal (T_amb i (wi_amb i) - wi_amb i * T_amb i (eval5_amb (pderiv 3 F5)) / eval5_amb (pderiv 3 F5)) :=
          isLegal_sub (T_amb_isLegal i (hwi_legal i)) hl_a
        rw [specX_sub hl_ab hl_b,
            specX_sub (T_amb_isLegal i (hwi_legal i)) hl_a,
            specX_div (isLegal_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)))
              (eval5_amb_isLegal _) hFx_X,
            specX_div (isLegal_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)))
              (isLegal_mul (isLegal_ofNat 2) (eval5_amb_isLegal _)) h2W2_X,
            specX_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)),
            specX_mul (hwi_legal i) (T_amb_isLegal i (eval5_amb_isLegal _)),
            specX_mul (isLegal_ofNat 2) (eval5_amb_isLegal _),
            specX_ofNat 2, hspec_T_wi, hspec_wi, hspec_T_eval5, hspec_T_eval5]
        simp only [ι_K5_toK5, map_sub, map_div₀, map_mul, map_ofNat]
      have hsplit : (⟨src_amb + ∑ i : Fin 4, tan_amb i, hnum_l⟩ : LegalAmb) =
          ⟨src_amb, hsrc_legal⟩ + ∑ i : Fin 4, ⟨tan_amb i, htan_legal i⟩ := by
        apply Subtype.ext
        simp only [Fin.sum_univ_four, Subring.coe_add]
      rw [hsplit, map_add, map_sum, hsrc_spec, Finset.sum_congr rfl fun i _ => htan_spec i,
        ← map_sum, ← map_add]
      change ι_K5 (srcX + resDivW w) = 0
      rw [heq, map_zero]
    rw [hnum_zero, zero_div]
  -- 6. Clear common legal denominator D of v_phys : Fin 6 → LegalAmb!
  choose a b hb hv_eq using fun k => hv_phys_legal k
  let D : Poly6 := ∏ k : Fin 6, b k
  let N : Fin 6 → Poly6 := fun k => a k * ∏ j ∈ Finset.univ.erase k, b j
  have hD_X : residueMap D ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun k _ => hb k
  have hD_A : toAmb D ≠ 0 := toAmb_ne_of_residue_ne hD_X
  have hND (k : Fin 6) : v_phys k = toAmb (N k) / toAmb D := by
    rw [hv_eq k]
    have hD_split : D = b k * ∏ j ∈ Finset.univ.erase k, b j :=
      (Finset.mul_prod_erase Finset.univ b (Finset.mem_univ k)).symm
    have hbk_A := toAmb_ne_of_residue_ne (hb k)
    have hprod_A : toAmb (∏ j ∈ Finset.univ.erase k, b j) ≠ 0 := by
      apply toAmb_ne_of_residue_ne
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun j _ => hb j
    rw [hD_split]; simp only [N, map_mul]; field_simp [hbk_A, hprod_A]
  -- 7. Normal equation in Poly6
  have hNormal : HodgeTestbed.directional sextic N = source * D := by
    apply IsFractionRing.injective Poly6 AmbientField
    change toAmb (HodgeTestbed.directional sextic N) = toAmb (source * D)
    have h1 : toAmb (HodgeTestbed.directional sextic N) =
        toAmb D * ∑ k : Fin 6, v_phys k * D_amb k (toAmb sextic) := by
      simp only [HodgeTestbed.directional, map_sum, map_mul, Finset.mul_sum, hND, D_amb_toAmb]
      apply Finset.sum_congr rfl; intro k _; field_simp [hD_A]
    rw [h1, hnorm_phys, map_mul]; ring
  -- 8. Divergence divisibility by sextic
  have hDiv_zero : residueMap (HodgeTestbed.divergenceNumerator D N) = 0 := by
    have hdiv_num_amb :
        toAmb (HodgeTestbed.divergenceNumerator D N) / toAmb D ^ 2 =
          ∑ k : Fin 6, D_amb k (v_phys k) := by
      simp only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
        HodgeTestbed.directional, hND, Derivation.leibniz_div, D_amb_toAmb,
        map_sub, map_sum, map_mul, smul_eq_mul]
      rw [div_eq_iff (pow_ne_zero 2 hD_A), Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _; field
    have hphys_zero : specX ⟨∑ k : Fin 6, D_amb k (v_phys k),
        isLegal_sum Finset.univ _ fun k _ => D_amb_isLegal k (hv_phys_legal k)⟩ = 0 := by
      have heqL : (⟨∑ k : Fin 6, D_amb k (v_phys k),
          isLegal_sum Finset.univ _ fun k _ => D_amb_isLegal k (hv_phys_legal k)⟩ : LegalAmb) =
          ⟨-(1 / 4 : AmbientField), hneg4_legal⟩ * ⟨QY_A, isLegal_toAmb QY⟩ ^ 2 *
            ⟨M_jac.det, M_jac_det_isLegal⟩ *
            ⟨∑ j : Fin 5, E_amb j.succ (v5 j),
              isLegal_sum Finset.univ _ fun j _ => E_amb_isLegal j.succ (hv5_legal j)⟩ :=
        Subtype.ext hdiv_phys
      rw [heqL, map_mul, hdiv5_zero, mul_zero]
    have hD2 : residueMap (D ^ 2) ≠ 0 := by rw [map_pow]; exact pow_ne_zero 2 hD_X
    have hspec_dn : specX ⟨∑ k : Fin 6, D_amb k (v_phys k),
        isLegal_sum Finset.univ _ fun k _ => D_amb_isLegal k (hv_phys_legal k)⟩ =
        residueMap (HodgeTestbed.divergenceNumerator D N) / residueMap (D ^ 2) := by
      change specXFun _ = _
      exact specXFun_eq _ hD2 (by rw [map_pow]; exact hdiv_num_amb.symm)
    rw [hspec_dn] at hphys_zero
    exact (div_eq_zero_iff.mp hphys_zero).resolve_right hD2
  obtain ⟨Q, hQ⟩ := (residueMap_eq_zero_iff _).mp hDiv_zero
  exact certificate_of_normalized D N Q hD_X hNormal hQ

end AmbientCalculus
end SymmetricSexticResidual.SymmetricPiola


theorem solution
    (w : Fin 4 → SymmetricSexticResidual.K5Field.K5)
    (heq : SymmetricSexticResidual.K5Field.srcX + SymmetricSexticResidual.K5Field.resDivW w = 0) :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.SymmetricSexticResidual.n)
      HodgeComputer.SymmetricSexticResidual.F
      HodgeComputer.SymmetricSexticResidual.A
      HodgeComputer.SymmetricSexticResidual.d
      HodgeComputer.SymmetricSexticResidual.q :=
  SymmetricSexticResidual.SymmetricPiola.certificate_of_K5_pde w heq
