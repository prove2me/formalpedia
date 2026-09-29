-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/eb62e098-69dd-52ac-a612-4cd49263a2b1

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
import Theorems.Thm_WittVector_exists_valuationSubring_lift_with_transcendental
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero
import Theorems.Thm_WeierstrassCurve_transcendental_j_perturb
import Theorems.Thm_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_map_veluQuotientOfSums
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u v

namespace AlphaNTransfer

private noncomputable abbrev jFKQ {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (N : ℕ)
    (Q : W.toAffine.Point) (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0) : F :=
  @WeierstrassCurve.j F _ (W.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩

private def ProdFormulaN {F : Type*} [Field F] [DecidableEq F] {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → W.toAffine.Point)
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) : Prop :=
  fibrePoly data.Φ W.j = ∏ i : ι, (X - C (jFKQ W N (Q i) (hΔ i)))

section MapPoint

variable {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S] (φ : R →+* S)
  (W : WeierstrassCurve R)

omit [DecidableEq R] [DecidableEq S] in
private theorem nonsingular_map {x y : R} (h : W.toAffine.Nonsingular x y) :
    (W.map φ).toAffine.Nonsingular (φ x) (φ y) :=
  (Affine.map_nonsingular (W := W.toAffine) (f := φ) φ.injective x y).mpr h

private def mapFun : W.toAffine.Point → (W.map φ).toAffine.Point
  | 0 => 0
  | .some x y h => .some (φ x) (φ y) (nonsingular_map φ W h)

omit [DecidableEq R] [DecidableEq S] in
private theorem mapFun_zero : mapFun φ W 0 = 0 := rfl

omit [DecidableEq R] [DecidableEq S] in
private theorem mapFun_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapFun φ W (.some x y h) = .some (φ x) (φ y) (nonsingular_map φ W h) := rfl

private theorem mapFun_add (P Q : W.toAffine.Point) :
    mapFun φ W (P + Q) = mapFun φ W P + mapFun φ W Q := by
  have hneg : ∀ x y : R, (W.map φ).toAffine.negY (φ x) (φ y) = φ (W.toAffine.negY x y) :=
    fun x y => Affine.map_negY (W' := W.toAffine) φ x y
  have hslope : ∀ x₁ x₂ y₁ y₂ : R,
      (W.map φ).toAffine.slope (φ x₁) (φ x₂) (φ y₁) (φ y₂) = φ (W.toAffine.slope x₁ x₂ y₁ y₂) :=
    fun x₁ x₂ y₁ y₂ => Affine.map_slope (W := W.toAffine) φ x₁ x₂ y₁ y₂
  have haddX : ∀ x₁ x₂ ℓ : R,
      (W.map φ).toAffine.addX (φ x₁) (φ x₂) (φ ℓ) = φ (W.toAffine.addX x₁ x₂ ℓ) :=
    fun x₁ x₂ ℓ => Affine.map_addX (W' := W.toAffine) φ x₁ x₂ ℓ
  have haddY : ∀ x₁ x₂ y₁ ℓ : R,
      (W.map φ).toAffine.addY (φ x₁) (φ x₂) (φ y₁) (φ ℓ) = φ (W.toAffine.addY x₁ x₂ y₁ ℓ) :=
    fun x₁ x₂ y₁ ℓ => Affine.map_addY (W' := W.toAffine) (f := φ) (x₁ := x₁) (x₂ := x₂)
      (y₁ := y₁) (ℓ := ℓ)
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact (Affine.Point.add_of_Y_eq (congrArg φ hxy.1) (by rw [hxy.2, hneg])).symm
  · have hxy' : ¬(φ x₁ = φ x₂ ∧ φ y₁ = (W.map φ).toAffine.negY (φ x₂) (φ y₂)) := fun h =>
      hxy ⟨φ.injective h.1, φ.injective (by rw [hneg] at h; exact h.2)⟩
    rw [Affine.Point.add_some hxy]
    show mapFun φ W _ = Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_some hxy', mapFun_some]
    congr 1
    · rw [hslope, haddX]
    · rw [hslope, haddY]

private def mapPoint : W.toAffine.Point →+ (W.map φ).toAffine.Point where
  toFun := mapFun φ W
  map_zero' := rfl
  map_add' := mapFun_add φ W

private theorem mapPoint_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapPoint φ W (.some x y h) = .some (φ x) (φ y) (nonsingular_map φ W h) := rfl

private theorem mapPoint_injective : Function.Injective (mapPoint φ W) := by
  intro P Q hPQ
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd hPQ.symm (Affine.Point.some_ne_zero _)
  · exact absurd hPQ (Affine.Point.some_ne_zero _)
  · have h := hPQ
    change Affine.Point.some (φ x₁) (φ y₁) _ = Affine.Point.some (φ x₂) (φ y₂) _ at h
    simp only [Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    cases φ.injective hx
    cases φ.injective hy
    rfl

private theorem coordsOrZero_mapPoint (P : W.toAffine.Point) :
    (mapPoint φ W P).coordsOrZero = Prod.map φ φ P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((0 : S), (0 : S)) = (φ 0, φ 0)
    simp
  · rfl

private theorem addOrderOf_mapPoint (P : W.toAffine.Point) :
    addOrderOf (mapPoint φ W P) = addOrderOf P :=
  addOrderOf_injective (mapPoint φ W) (mapPoint_injective φ W) P

private theorem oddOrderSummingSet_mapPoint (Q : W.toAffine.Point) (n : ℕ) :
    (W.map φ).oddOrderSummingSet (mapPoint φ W Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map φ φ) := by
  simp only [WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  show (k • mapPoint φ W Q).coordsOrZero = Prod.map φ φ (k • Q).coordsOrZero
  rw [← map_nsmul, coordsOrZero_mapPoint]

end MapPoint

section Carrier

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)

private theorem map_veluGx (x y : R) : φ (W.veluGx x y) = (W.map φ).veluGx (φ x) (φ y) := by
  simp [WeierstrassCurve.veluGx, map_ofNat]

private theorem map_veluGy (x y : R) : φ (W.veluGy x y) = (W.map φ).veluGy (φ x) (φ y) := by
  simp [WeierstrassCurve.veluGy, map_ofNat]

private theorem map_asymWeight (x y : R) :
    φ (x * W.veluGx x y - y * W.veluGy x y) =
      φ x * (W.map φ).veluGx (φ x) (φ y) - φ y * (W.map φ).veluGy (φ x) (φ y) := by
  rw [map_sub, map_mul, map_mul, map_veluGx, map_veluGy]

private def fkqOfSet (T : Finset (R × R)) : WeierstrassCurve R :=
  W.veluQuotientOfSums (∑ P ∈ T, W.veluGx P.1 P.2)
    (∑ P ∈ T, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))

private theorem fullKernelQuotient_eq_fkqOfSet {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F)
    (Q : V.toAffine.Point) (N : ℕ) :
    V.fullKernelQuotient Q N = fkqOfSet V (V.oddOrderSummingSet Q (N - 1)) := rfl

variable [DecidableEq S]

private theorem fkqOfSet_map (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    (fkqOfSet W T).map φ = fkqOfSet (W.map φ) (T.image (Prod.map φ φ)) := by
  unfold fkqOfSet
  rw [W.map_veluQuotientOfSums φ, map_sum, map_sum, Finset.sum_image hφ, Finset.sum_image hφ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    rintro ⟨x, y⟩ -
    exact map_veluGx φ W x y
  · refine Finset.sum_congr rfl ?_
    rintro ⟨x, y⟩ -
    exact map_asymWeight φ W x y

end Carrier

section CarrierField

variable {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S] (φ : R →+* S)
  (W : WeierstrassCurve R)

private theorem fullKernelQuotient_map (Q : W.toAffine.Point) (N : ℕ) :
    (W.fullKernelQuotient Q N).map φ = (W.map φ).fullKernelQuotient (mapPoint φ W Q) N := by
  rw [fullKernelQuotient_eq_fkqOfSet, fullKernelQuotient_eq_fkqOfSet, oddOrderSummingSet_mapPoint]
  exact fkqOfSet_map φ W _ (Function.Injective.prodMap φ.injective φ.injective).injOn

private theorem fullKernelQuotient_mapPoint_Δ (Q : W.toAffine.Point) (N : ℕ) :
    ((W.map φ).fullKernelQuotient (mapPoint φ W Q) N).Δ = φ (W.fullKernelQuotient Q N).Δ := by
  rw [← fullKernelQuotient_map, WeierstrassCurve.map_Δ]

private theorem fullKernelQuotient_mapPoint_Δ_ne_zero (Q : W.toAffine.Point) (N : ℕ)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0) :
    ((W.map φ).fullKernelQuotient (mapPoint φ W Q) N).Δ ≠ 0 := by
  rw [fullKernelQuotient_mapPoint_Δ]
  exact (map_ne_zero φ).mpr hΔ

end CarrierField

private theorem isRoot_map_iff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (Φ : Polynomial (Polynomial ℤ)) (a b : R) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (φ a))).IsRoot (φ b) ↔
      (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).IsRoot b := by
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom S) (φ a) =
      φ.comp (Polynomial.eval₂RingHom (Int.castRingHom R) a) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp
    · simp
  rw [hcomp, ← Polynomial.map_map, Polynomial.IsRoot.def, Polynomial.IsRoot.def, Polynomial.eval_map,
    Polynomial.eval₂_hom, map_eq_zero_iff φ hφ]

private theorem j_congr {F : Type*} [Field F] {A B : WeierstrassCurve F} (h : A = B)
    (hA : A.IsElliptic) (hB : B.IsElliptic) :
    @WeierstrassCurve.j F _ A hA = @WeierstrassCurve.j F _ B hB := by
  subst h
  rfl

private theorem fibrePoly_map_ringHom {R : Type*} [CommRing R] {κ : Type*} [Field κ] (f : R →+* κ)
    (Φ : Polynomial (Polynomial ℤ)) (a : R) :
    fibrePoly Φ (f a) = (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).map f := by
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom κ) (f a) =
      f.comp (Polynomial.eval₂RingHom (Int.castRingHom R) a) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp
    · simp
  rw [fibrePoly, hcomp, ← Polynomial.map_map]

private theorem fibrePoly_map {K : Type*} [Field K] {κ : Type*} [Field κ] (ι : K →+* κ)
    (Φ : Polynomial (Polynomial ℤ)) (a : K) :
    fibrePoly Φ (ι a) = (fibrePoly Φ a).map ι :=
  fibrePoly_map_ringHom ι Φ a

private theorem jFKQ_mapPoint {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S] (φ : R →+* S)
    (W : WeierstrassCurve R) (Q : W.toAffine.Point) (N : ℕ) (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (hΔ' : ((W.map φ).fullKernelQuotient (mapPoint φ W Q) N).Δ ≠ 0) :
    jFKQ (W.map φ) N (mapPoint φ W Q) hΔ' = φ (jFKQ W N Q hΔ) := by
  unfold jFKQ
  haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  rw [j_congr (fullKernelQuotient_map φ W Q N).symm ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ inferInstance,
    WeierstrassCurve.map_j]

private theorem addOrderOf_eq_of_nsmul_eq_zero_of_addOrderOf_map {G H : Type*} [AddMonoid G] [AddMonoid H]
    (f : G →+ H) {x : G} {N : ℕ} (hx : N • x = 0) (hfx : addOrderOf (f x) = N) :
    addOrderOf x = N := by
  apply Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hx)
  rw [← hfx]
  exact addOrderOf_dvd_of_nsmul_eq_zero (by rw [← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero])

private theorem zmultiples_injective_of_map {G H : Type*} [AddGroup G] [AddGroup H] (f : G →+ H)
    {ι : Type*} {Q : ι → G} {Q' : ι → H} (hf : ∀ i, f (Q i) = Q' i)
    (hinj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i)) :
    Function.Injective fun i => AddSubgroup.zmultiples (Q i) := by
  intro i i' h
  apply hinj
  simp only at h ⊢
  have := congrArg (AddSubgroup.map f) h
  rwa [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples, hf i, hf i'] at this

private theorem zmultiples_map_injective {G H : Type*} [AddGroup G] [AddGroup H] (f : G →+ H)
    (hf : Function.Injective f) {ι : Type*} {Q : ι → G}
    (hinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i)) :
    Function.Injective fun i => AddSubgroup.zmultiples (f (Q i)) := by
  intro i j hij
  apply hinj
  have h1 : ∀ k, AddSubgroup.zmultiples (f (Q k)) = (AddSubgroup.zmultiples (Q k)).map f := fun k =>
    (AddMonoidHom.map_zmultiples f (Q k)).symm
  simp only [h1] at hij
  exact AddSubgroup.map_injective hf hij

private theorem nsmul_injOn_of_lt {G : Type*} [AddGroup G] (g : G) {m₁ m₂ : ℕ}
    (h₁ : m₁ < addOrderOf g) (h₂ : m₂ < addOrderOf g) (h : m₁ • g = m₂ • g) : m₁ = m₂ := by
  wlog hle : m₁ ≤ m₂ generalizing m₁ m₂
  · exact (this h₂ h₁ h.symm (le_of_lt (not_le.mp hle))).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hd : d • g = 0 := by
    rw [add_nsmul] at h
    exact (add_eq_left.mp h.symm)
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rfl
  · exact absurd (Nat.le_of_dvd hdpos hdvd) (by omega)

private theorem prodFormulaN_of_map
    {K : Type*} [Field K] [DecidableEq K] {κ : Type*} [Field κ] [DecidableEq κ]
    (ιh : K →+* κ) {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → W.toAffine.Point)
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0)
    (hΔ' : ∀ i, ((W.map ιh).fullKernelQuotient (mapPoint ιh W (Q i)) N).Δ ≠ 0)
    (h : ProdFormulaN data (W.map ιh) (fun i => mapPoint ιh W (Q i)) hΔ') :
    ProdFormulaN data W Q hΔ := by
  classical
  unfold ProdFormulaN at h ⊢
  apply Polynomial.map_injective ιh ιh.injective
  rw [← fibrePoly_map, ← WeierstrassCurve.map_j, h, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, jFKQ_mapPoint ιh W (Q i) N (hΔ i) (hΔ' i)]

private theorem exists_map_eq_fullKernelQuotient_and_map_residue_eq_fullKernelQuotient_reduceHom
    {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = N) :
    ∃ V : WeierstrassCurve A,
      V.map A.subtype = (W.map A.subtype).fullKernelQuotient Q N ∧
      V.map (residue A) =
        (W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N := by
  classical
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  have hQN : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hQ₀ord : addOrderOf (reduceHom hΔ Q) = N := _root_.WeierstrassCurve.addOrderOf_reduceHom_of_natCast_ne_zero hΔ hN hQ

  have hmem : ∀ m : ℕ, 1 ≤ m → m ≤ N - 1 →
      ∃ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y) (_ : x ∈ A), m • Q = .some x y h := by
    intro m hm1 hmn
    have hne : m • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
    rcases hP : m • Q with _ | ⟨x, y, h⟩
    · exact absurd hP hne
    · refine ⟨x, y, h, ?_, rfl⟩
      refine WeierstrassCurve.X_mem_of_nsmul_eq_zero' W hN h ?_
      rw [← hP, smul_smul, mul_comm, ← smul_smul, hQN, smul_zero]

  let sec : L → A := fun z => if hz : z ∈ A then ⟨z, hz⟩ else 0
  have hsec : ∀ {z : L} (hz : z ∈ A), sec z = ⟨z, hz⟩ := fun hz => dif_pos hz
  let TA : Finset (A × A) := (Finset.Icc 1 (N - 1)).image fun m => Prod.map sec sec (m • Q).coordsOrZero

  have hTsub : TA.image (Prod.map A.subtype A.subtype) = (W.map A.subtype).oddOrderSummingSet Q (N - 1) := by
    simp only [TA, WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
    refine Finset.image_congr fun m hm => ?_
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    obtain ⟨x, y, h, hx, hP⟩ := hmem m hm.1 hm.2
    have hy : y ∈ A := WeierstrassCurve.Affine.Y_mem_of_X_mem W h.1 hx
    show Prod.map A.subtype A.subtype (Prod.map sec sec (m • Q).coordsOrZero) = (m • Q).coordsOrZero
    rw [hP, Affine.Point.coordsOrZero_some, Prod.map_apply, Prod.map_apply, hsec hx, hsec hy]
    rfl

  have hr : ∀ {m : ℕ} {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A),
      m • Q = .some x y h →
      Prod.map (residue A) (residue A) (Prod.map sec sec (m • Q).coordsOrZero)
        = (m • reduceHom hΔ Q).coordsOrZero := by
    intro m x y h hx hP
    have hy : y ∈ A := WeierstrassCurve.Affine.Y_mem_of_X_mem W h.1 hx
    rw [← map_nsmul, hP, Affine.Point.coordsOrZero_some, Prod.map_apply, Prod.map_apply, hsec hx, hsec hy]
    show _ = (WeierstrassCurve.reducePoint hΔ (Affine.Point.some x y h)).coordsOrZero
    rw [WeierstrassCurve.reducePoint_some_of_mem hΔ h hx, Affine.Point.coordsOrZero_some]

  have hTres : TA.image (Prod.map (residue A) (residue A)) =
      (W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) (N - 1) := by

    change ((Finset.Icc 1 (N - 1)).image fun m => Prod.map sec sec (m • Q).coordsOrZero).image
        (Prod.map (residue A) (residue A)) =
      (Finset.Icc 1 (N - 1)).image fun k => (k • reduceHom hΔ Q).coordsOrZero
    rw [Finset.image_image]
    refine Finset.image_congr fun m hm => ?_
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    obtain ⟨x, y, h, hx, hP⟩ := hmem m hm.1 hm.2
    exact hr h hx hP

  have hTinj : Set.InjOn (Prod.map (residue A) (residue A)) ↑TA := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe] at ht₁ ht₂
    simp only [TA, Finset.mem_image, Finset.mem_Icc] at ht₁ ht₂
    obtain ⟨m₁, hm₁, rfl⟩ := ht₁
    obtain ⟨m₂, hm₂, rfl⟩ := ht₂
    obtain ⟨x₁, y₁, h₁, hx₁, hP₁⟩ := hmem m₁ hm₁.1 hm₁.2
    obtain ⟨x₂, y₂, h₂, hx₂, hP₂⟩ := hmem m₂ hm₂.1 hm₂.2
    rw [hr h₁ hx₁ hP₁, hr h₂ hx₂ hP₂] at heq
    have hne : ∀ {m : ℕ}, 1 ≤ m → m ≤ N - 1 → m • reduceHom hΔ Q ≠ 0 := fun hm1 hmn =>
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ₀ord]; omega)
    have hmm : m₁ = m₂ :=
      nsmul_injOn_of_lt (reduceHom hΔ Q) (by rw [hQ₀ord]; omega) (by rw [hQ₀ord]; omega)
        (WeierstrassCurve.eq_of_coordsOrZero_eq (hne hm₁.1 hm₁.2) (hne hm₂.1 hm₂.2) heq)
    rw [hmm]

  refine ⟨fkqOfSet W TA, ?_, ?_⟩
  · rw [fullKernelQuotient_eq_fkqOfSet, ← hTsub]
    exact fkqOfSet_map A.subtype W TA
      ((Function.Injective.prodMap A.subtype_injective A.subtype_injective).injOn)
  · rw [fullKernelQuotient_eq_fkqOfSet, fkqOfSet_map (residue A) W TA hTinj, hTres]

private theorem spec_specialFibre
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {L : Type u} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (WA : WeierstrassCurve A) (hΔA : (WA.map (residue A)).Δ ≠ 0)
    {N : ℕ} [NeZero N] (hNκ : (N : ResidueField A) ≠ 0)
    (data : ModularPolynomialData N)
    (htr : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype)
        ⟨isUnit_iff_ne_zero.mpr hΔL⟩))
    {ι : Type v} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    [hE : (WA.map (residue A)).IsElliptic]
    (Q' : ι → (WA.map (residue A)).toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = N)
    (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
    (hΔ' : ∀ i, ((WA.map (residue A)).fullKernelQuotient (Q' i) N).Δ ≠ 0) :
    fibrePoly data.Φ (WA.map (residue A)).j =
      ∏ i, (X - C (@WeierstrassCurve.j (ResidueField A) _
        ((WA.map (residue A)).fullKernelQuotient (Q' i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩)) := by
  classical

  have hresΔ : residue A WA.Δ ≠ 0 := by rwa [← map_Δ]
  have hΔunit : IsUnit WA.Δ := by
    by_contra h
    exact hresΔ ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
  haveI hWA : WA.IsElliptic := ⟨hΔunit⟩
  have hΔL : (WA.map A.subtype).Δ ≠ 0 := by
    rw [map_Δ]
    intro h
    exact hΔunit.ne_zero (Subtype.val_injective (by simpa using h))
  haveI : (WA.map A.subtype).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔL⟩

  have hlift' : ∀ i, ∃ Qt : (WA.map A.subtype).toAffine.Point,
      N • Qt = 0 ∧ reduceHom hΔA Qt = Q' i := fun i =>
    WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero A WA hΔA hNκ (Q' i)
      (by rw [← hQ' i]; exact addOrderOf_nsmul_eq_zero (Q' i))
  choose Qt hQt using hlift'

  have hQt_ord : ∀ i, addOrderOf (Qt i) = N := by
    intro i
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero (hQt i).1) ?_
    rw [← hQ' i, ← (hQt i).2]
    exact addOrderOf_dvd_of_nsmul_eq_zero
      (by rw [← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero])
  have hQt_inj : Function.Injective fun i => AddSubgroup.zmultiples (Qt i) := by
    intro i i' h
    apply hQ'inj
    simp only at h ⊢
    have := congrArg (AddSubgroup.map (reduceHom hΔA)) h
    rwa [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples, (hQt i).2, (hQt i').2] at this

  have hS : ∀ i, ∃ V : WeierstrassCurve A,
      V.map A.subtype = (WA.map A.subtype).fullKernelQuotient (Qt i) N ∧
      V.map (residue A) =
        (WA.map (residue A)).fullKernelQuotient (reduceHom hΔA (Qt i)) N := fun i =>
    exists_map_eq_fullKernelQuotient_and_map_residue_eq_fullKernelQuotient_reduceHom
      A WA hΔA hNκ (Qt i) (hQt_ord i)
  choose V hV using hS
  have hVres : ∀ i, (V i).map (residue A) =
      (WA.map (residue A)).fullKernelQuotient (Q' i) N := by
    intro i; rw [(hV i).2, (hQt i).2]
  have hVunit : ∀ i, IsUnit (V i).Δ := by
    intro i
    by_contra h
    apply hΔ' i
    rw [← hVres i, map_Δ]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h)
  haveI hVell : ∀ i, (V i).IsElliptic := fun i => ⟨hVunit i⟩

  have hΔt : ∀ i, ((WA.map A.subtype).fullKernelQuotient (Qt i) N).Δ ≠ 0 := by
    intro i
    rw [← (hV i).1, map_Δ]
    exact fun h => (hVunit i).ne_zero (Subtype.val_injective (by simpa using h))

  let e := (Fintype.equivFin ι).symm
  have hιF : Fintype.card (Fin (Fintype.card ι)) = dedekindPsi N := by simpa using hι
  have hT0 := h0 (K₀ := L) data (WA.map A.subtype) (htr hΔL)
    (ι := Fin (Fintype.card ι)) hιF (fun k => Qt (e k))
    (fun k => hQt_ord (e k))
    (fun k k' h => e.injective (hQt_inj h))
    (fun k => hΔt (e k))
  have hT : fibrePoly data.Φ (WA.map A.subtype).j =
      ∏ i, (X - C (@WeierstrassCurve.j L _ ((WA.map A.subtype).fullKernelQuotient (Qt i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔt i)⟩)) := by
    rw [hT0]
    exact Fintype.prod_equiv e _ _ fun k => rfl

  have hjgen : ∀ i, @WeierstrassCurve.j L _ ((WA.map A.subtype).fullKernelQuotient (Qt i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔt i)⟩ = A.subtype (V i).j := by
    intro i
    have : ∀ (V' : WeierstrassCurve L) (_ : V' = (V i).map A.subtype) (h' : V'.IsElliptic),
        @WeierstrassCurve.j L _ V' h' = A.subtype (V i).j := by
      rintro V' rfl h'; exact WeierstrassCurve.map_j (V i) A.subtype
    exact this _ (hV i).1.symm _
  have hjres : ∀ i, @WeierstrassCurve.j (ResidueField A) _
        ((WA.map (residue A)).fullKernelQuotient (Q' i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩
      = residue A (V i).j := by
    intro i
    have : ∀ (V' : WeierstrassCurve (ResidueField A)) (_ : V' = (V i).map (residue A))
        (h' : V'.IsElliptic), @WeierstrassCurve.j _ _ V' h' = residue A (V i).j := by
      rintro V' rfl h'; exact WeierstrassCurve.map_j (V i) (residue A)
    exact this _ (hVres i).symm _
  set PA : Polynomial A := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) WA.j) with hPA
  set QA : Polynomial A := ∏ i, (X - C (V i).j) with hQA
  have hPAmap : ∀ {S : Type _} [CommRing S] (g : A →+* S),
      PA.map g = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (g WA.j)) := by
    intro S _ g
    rw [hPA, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext n; simp
    · simp
  have hPAgen : PA.map A.subtype = fibrePoly data.Φ (WA.map A.subtype).j := by
    rw [hPAmap, WeierstrassCurve.map_j]; rfl
  have hPAres : PA.map (residue A) = fibrePoly data.Φ (WA.map (residue A)).j := by
    rw [hPAmap]
    have : (WA.map (residue A)).j = residue A WA.j := WeierstrassCurve.map_j WA (residue A)
    rw [this]; rfl
  have hQAgen : QA.map A.subtype = ∏ i, (X - C (@WeierstrassCurve.j L _
      ((WA.map A.subtype).fullKernelQuotient (Qt i) N) ⟨isUnit_iff_ne_zero.mpr (hΔt i)⟩)) := by
    rw [hQA, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjgen i]
  have hQAres : QA.map (residue A) = ∏ i, (X - C (@WeierstrassCurve.j (ResidueField A) _
      ((WA.map (residue A)).fullKernelQuotient (Q' i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩)) := by
    rw [hQA, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjres i]
  have hPQ : PA = QA := by
    apply Polynomial.map_injective A.subtype Subtype.val_injective
    rw [hPAgen, hQAgen]; exact hT
  rw [← hPAres, ← hQAres, hPQ]

private theorem main_charZero
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K] {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type v} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  classical
  obtain ⟨L, _, _, _, A, φ, hφ, ιh, hι_res, t, htA, htm, htr⟩ :=
    _root_.WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero K
  letI : DecidableEq L := Classical.decEq _
  letI : DecidableEq (ResidueField A) := Classical.decEq _
  let tA : A := ⟨t, htA⟩
  let WA : WeierstrassCurve A :=
    ⟨⟨φ W.a₁, hφ _⟩, ⟨φ W.a₂, hφ _⟩, ⟨φ W.a₃, hφ _⟩, ⟨φ W.a₄, hφ _⟩ + tA, ⟨φ W.a₆, hφ _⟩ + tA ^ 2⟩
  have htres : residue A tA = 0 := (residue_eq_zero_iff (R := A) tA).mpr htm
  have hWA_res : WA.map (residue A) = W.map ιh := by
    ext <;> simp [WA, WeierstrassCurve.map, hι_res, htres]
  have hWA_gen : WA.map A.subtype = ⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ := by
    ext <;> rfl
  obtain ⟨hΔgen, hJ⟩ := _root_.WeierstrassCurve.transcendental_j_perturb (R := K) φ t htr W
  have htrWA : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype)
        ⟨isUnit_iff_ne_zero.mpr hΔL⟩) := by
    intro hΔL
    rwa [j_congr hWA_gen ⟨isUnit_iff_ne_zero.mpr hΔL⟩ ⟨isUnit_iff_ne_zero.mpr hΔgen⟩]
  have hΔA : (WA.map (residue A)).Δ ≠ 0 := by
    rw [hWA_res, WeierstrassCurve.map_Δ]
    exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero
  have hNκ : (N : ResidueField A) ≠ 0 := by
    rw [← map_natCast ιh, _root_.map_ne_zero]
    exact Nat.cast_ne_zero.mpr (NeZero.ne N)
  haveI hEres : (W.map ιh).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by
    rw [WeierstrassCurve.map_Δ]
    exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero)⟩
  have key : ∀ (Xc : WeierstrassCurve (ResidueField A)) (hX : WA.map (residue A) = Xc)
      [Xc.IsElliptic] (Q' : ι → Xc.toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = N)
      (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
      (hΔ' : ∀ i, (Xc.fullKernelQuotient (Q' i) N).Δ ≠ 0),
      fibrePoly data.Φ Xc.j =
        ∏ i, (X - C (@WeierstrassCurve.j (ResidueField A) _ (Xc.fullKernelQuotient (Q' i) N)
          ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩)) := by
    rintro Xc rfl _ Q' hQ' hQ'inj hΔ'
    exact spec_specialFibre h0 A WA hΔA hNκ data htrWA hι Q' hQ' hQ'inj hΔ'
  have hQ'ord : ∀ i, addOrderOf (mapPoint ιh W (Q i)) = N := fun i => by
    rw [addOrderOf_mapPoint, hQ i]
  have hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ιh W (Q i)) := by
    intro i j hij
    apply hQinj
    have h1 : ∀ k, AddSubgroup.zmultiples (mapPoint ιh W (Q k))
        = (AddSubgroup.zmultiples (Q k)).map (mapPoint ιh W) := fun k =>
      (AddMonoidHom.map_zmultiples (mapPoint ιh W) (Q k)).symm
    simp only [h1] at hij
    exact AddSubgroup.map_injective (mapPoint_injective ιh W) hij
  have hΔ' : ∀ i, ((W.map ιh).fullKernelQuotient (mapPoint ιh W (Q i)) N).Δ ≠ 0 := fun i =>
    fullKernelQuotient_mapPoint_Δ_ne_zero ιh W (Q i) N (hΔ i)
  have hmain' := key (W.map ιh) hWA_res (fun i => mapPoint ιh W (Q i)) hQ'ord hQ'inj hΔ'
  have hPF : ProdFormulaN data (W.map ιh) (fun i => mapPoint ιh W (Q i)) hΔ' := by
    unfold ProdFormulaN jFKQ
    exact hmain'
  have hout := prodFormulaN_of_map ιh data W Q hΔ hΔ' hPF
  unfold ProdFormulaN jFKQ at hout
  exact hout

private theorem main_charP
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (data : ModularPolynomialData N) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type v} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  classical
  haveI : PerfectRing K p := IsAlgClosed.perfectRing K p
  obtain ⟨L, _, _, _, A, φ, hφ, ιh, hι_res, t, htA, htm, htr⟩ :=
    _root_.WittVector.exists_valuationSubring_lift_with_transcendental p K
  letI : DecidableEq L := Classical.decEq _
  letI : DecidableEq (ResidueField A) := Classical.decEq _
  haveI : CharZero (WittVector p K) := φ.charZero
  have hφinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have hC : (Polynomial.C (a - b) : Polynomial (WittVector p K)) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (sub_ne_zero.mpr hne)
    have hev := htr _ hC
    rw [Polynomial.eval₂_C] at hev
    exact hev (by rw [map_sub, hab, sub_self])
  haveI : IsDomain (WittVector p K) := Function.Injective.isDomain φ hφinj
  let τ : K → WittVector p K := WittVector.teichmuller p
  let W𝕎 : WeierstrassCurve (WittVector p K) := ⟨τ W.a₁, τ W.a₂, τ W.a₃, τ W.a₄, τ W.a₆⟩
  let tA : A := ⟨t, htA⟩
  let WA : WeierstrassCurve A :=
    ⟨⟨φ (τ W.a₁), hφ _⟩, ⟨φ (τ W.a₂), hφ _⟩, ⟨φ (τ W.a₃), hφ _⟩,
     ⟨φ (τ W.a₄), hφ _⟩ + tA, ⟨φ (τ W.a₆), hφ _⟩ + tA ^ 2⟩
  have htres : residue A tA = 0 := (residue_eq_zero_iff (R := A) tA).mpr htm
  have hWA_res : WA.map (residue A) = W.map ιh := by
    ext <;> simp [WA, τ, WeierstrassCurve.map, hι_res, htres]
  have hWA_gen : WA.map A.subtype =
      ⟨φ W𝕎.a₁, φ W𝕎.a₂, φ W𝕎.a₃, φ W𝕎.a₄ + t, φ W𝕎.a₆ + t ^ 2⟩ := by
    ext <;> rfl
  obtain ⟨hΔgen, hJ⟩ :=
    _root_.WeierstrassCurve.transcendental_j_perturb (R := WittVector p K) φ t htr W𝕎
  have htrWA : ∀ hΔL : (WA.map A.subtype).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _ (WA.map A.subtype)
        ⟨isUnit_iff_ne_zero.mpr hΔL⟩) := by
    intro hΔL
    rwa [j_congr hWA_gen ⟨isUnit_iff_ne_zero.mpr hΔL⟩ ⟨isUnit_iff_ne_zero.mpr hΔgen⟩]
  have hΔA : (WA.map (residue A)).Δ ≠ 0 := by
    rw [hWA_res, WeierstrassCurve.map_Δ]
    exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero
  have hNκ : (N : ResidueField A) ≠ 0 := by
    rw [← map_natCast ιh, _root_.map_ne_zero]
    exact hN
  haveI hEres : (W.map ιh).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by
    rw [WeierstrassCurve.map_Δ]
    exact (_root_.map_ne_zero ιh).mpr W.isUnit_Δ.ne_zero)⟩
  have key : ∀ (Xc : WeierstrassCurve (ResidueField A)) (hX : WA.map (residue A) = Xc)
      [Xc.IsElliptic] (Q' : ι → Xc.toAffine.Point) (hQ' : ∀ i, addOrderOf (Q' i) = N)
      (hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (Q' i))
      (hΔ' : ∀ i, (Xc.fullKernelQuotient (Q' i) N).Δ ≠ 0),
      fibrePoly data.Φ Xc.j =
        ∏ i, (X - C (@WeierstrassCurve.j (ResidueField A) _ (Xc.fullKernelQuotient (Q' i) N)
          ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩)) := by
    rintro Xc rfl _ Q' hQ' hQ'inj hΔ'
    exact spec_specialFibre h0 A WA hΔA hNκ data htrWA hι Q' hQ' hQ'inj hΔ'
  have hQ'ord : ∀ i, addOrderOf (mapPoint ιh W (Q i)) = N := fun i => by
    rw [addOrderOf_mapPoint, hQ i]
  have hQ'inj : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ιh W (Q i)) := by
    intro i j hij
    apply hQinj
    have h1 : ∀ k, AddSubgroup.zmultiples (mapPoint ιh W (Q k))
        = (AddSubgroup.zmultiples (Q k)).map (mapPoint ιh W) := fun k =>
      (AddMonoidHom.map_zmultiples (mapPoint ιh W) (Q k)).symm
    simp only [h1] at hij
    exact AddSubgroup.map_injective (mapPoint_injective ιh W) hij
  have hΔ' : ∀ i, ((W.map ιh).fullKernelQuotient (mapPoint ιh W (Q i)) N).Δ ≠ 0 := fun i =>
    fullKernelQuotient_mapPoint_Δ_ne_zero ιh W (Q i) N (hΔ i)
  have hmain' := key (W.map ιh) hWA_res (fun i => mapPoint ιh W (Q i)) hQ'ord hQ'inj hΔ'
  have hPF : ProdFormulaN data (W.map ιh) (fun i => mapPoint ιh W (Q i)) hΔ' := by
    unfold ProdFormulaN jFKQ
    exact hmain'
  have hout := prodFormulaN_of_map ιh data W Q hΔ hΔ' hPF
  unfold ProdFormulaN jFKQ at hout
  exact hout

end AlphaNTransfer

theorem solution (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (data : ModularPolynomialData N) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · haveI := Fact.mk hprime
    exact AlphaNTransfer.main_charP h0 p hN data W hι Q hQ hQinj hΔ
  · haveI : CharZero K := CharP.charP_to_charZero K
    exact AlphaNTransfer.main_charZero h0 data W hι Q hQ hQinj hΔ

end S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental (solution)
