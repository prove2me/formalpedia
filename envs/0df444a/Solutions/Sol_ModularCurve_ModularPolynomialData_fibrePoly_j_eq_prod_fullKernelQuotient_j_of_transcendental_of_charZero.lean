-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8c66d4b7-9b69-5317-a13e-6eaf4175135a

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_TatePoint
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Definitions.Def_ModularCurve_SpecialisationBridge
import Theorems.Thm_ModularCurve_TatePoint_fullKernelIsRootAt
import Theorems.Thm_ModularCurve_TatePoint_fullKernelInjAt
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero"

set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero.ModularCurve ModularCurve.TatePoint WeierstrassCurve WeierstrassCurve.Affine"
open scoped Classical

universe u

namespace ModularCurve
p2m_export "ModularCurve" "dedekindPsi ModularPolynomialData fibrePoly B3.vcAddEquiv B3.pointAddEquivOfEq B3.pointAddEquivOfEq_rfl TatePoint.fullKernelIsRootAt TatePoint.isAlgClosed_H TatePoint.charZero_H TatePoint.fullKernelInjAt"
namespace FKQTransport
p2m_open "ModularCurve"

attribute [local instance] ModularCurve.TatePoint.isAlgClosed_H ModularCurve.TatePoint.charZero_H

private theorem roots_fibrePoly_j_eq_of_transcendental
    {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (E : WeierstrassCurve H) [E.IsElliptic] (hj : Transcendental Qbar E.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → E.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (E.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    (fibrePoly data.Φ E.j).roots =
      Finset.univ.val.map (fun i => @WeierstrassCurve.j H _ (E.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩) := by
  set jQ : ι → H := fun i => @WeierstrassCurve.j H _ (E.fullKernelQuotient (Q i) N)
    ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩ with hjQ
  have hmonic : (fibrePoly data.Φ E.j).Monic := data.monic.map _
  have hdeg : (fibrePoly data.Φ E.j).natDegree = dedekindPsi N := by
    rw [fibrePoly, data.monic.natDegree_map, data.natDegree_eq]
  have hcard : (fibrePoly data.Φ E.j).roots.card = dedekindPsi N := by
    rw [← hdeg]
    exact (splits_iff_card_roots.mp (IsAlgClosed.splits (fibrePoly data.Φ E.j)))

  have hroot : ∀ i, (fibrePoly data.Φ E.j).IsRoot (jQ i) := fun i =>
    ModularCurve.TatePoint.fullKernelIsRootAt N E (Q i) (hQ i) (hΔ i) data

  have hjQinj : Function.Injective jQ := by
    intro i i' h
    exact hQinj (ModularCurve.TatePoint.fullKernelInjAt N E
      (transcendental_rat_of_transcendental_qbar hj) (Q i) (Q i') (hQ i) (hQ i')
      (hΔ i) (hΔ i') h)

  have hnodup : (Finset.univ.val.map jQ).Nodup := Finset.univ.nodup.map hjQinj

  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  ·
    refine Multiset.le_iff_count.mpr fun y => ?_
    by_cases hy : y ∈ Finset.univ.val.map jQ
    · obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hy
      calc (Finset.univ.val.map jQ).count (jQ i)
          ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnodup (jQ i)
        _ ≤ (fibrePoly data.Φ E.j).roots.count (jQ i) :=
          Multiset.one_le_count_iff_mem.mpr
            ((mem_roots hmonic.ne_zero).mpr (hroot i))
    · rw [Multiset.count_eq_zero_of_notMem hy]
      exact Nat.zero_le _
  ·
    rw [hcard, Multiset.card_map, ← Finset.card_def, Finset.card_univ, hι]

private theorem fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
    {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (E : WeierstrassCurve H) [E.IsElliptic] (hj : Transcendental Qbar E.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → E.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (E.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ E.j =
      ∏ i, (X - C (@WeierstrassCurve.j H _ (E.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  have hmonic : (fibrePoly data.Φ E.j).Monic := data.monic.map _
  have hdeg : (fibrePoly data.Φ E.j).natDegree = dedekindPsi N := by
    rw [fibrePoly, data.monic.natDegree_map, data.natDegree_eq]
  have hcard : (fibrePoly data.Φ E.j).roots.card = dedekindPsi N := by
    rw [← hdeg]
    exact (splits_iff_card_roots.mp (IsAlgClosed.splits (fibrePoly data.Φ E.j)))
  calc fibrePoly data.Φ E.j
      = ((fibrePoly data.Φ E.j).roots.map fun a => X - C a).prod :=
        (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
          (hcard.trans hdeg.symm)).symm
    _ = ((Finset.univ.val.map fun i => @WeierstrassCurve.j H _ (E.fullKernelQuotient (Q i) N)
          ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩).map fun a => X - C a).prod := by
        rw [roots_fibrePoly_j_eq_of_transcendental data E hj hι Q hQ hQinj hΔ]
    _ = (Finset.univ.val.map fun i => X - C (@WeierstrassCurve.j H _
          (E.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)).prod := by
        rw [Multiset.map_map]; rfl
    _ = ∏ i, (X - C (@WeierstrassCurve.j H _ (E.fullKernelQuotient (Q i) N)
          ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := (Finset.prod_eq_multiset_prod _ _).symm

section MapTransport

variable {L K₀ : Type*} [Field L] [Field K₀] [DecidableEq L] [DecidableEq K₀]

private noncomputable def ptMap (f : L →+* K₀) (W : WeierstrassCurve L) :
    W.toAffine.Point →+ (W.map f).toAffine.Point :=
  letI : Algebra L K₀ := f.toAlgebra
  WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId L K₀)

private theorem ptMap_zero (f : L →+* K₀) (W : WeierstrassCurve L) : ptMap f W 0 = 0 :=
  rfl

private theorem ptMap_some (f : L →+* K₀) (W : WeierstrassCurve L) {x y : L}
    (h : W.toAffine.Nonsingular x y) :
    ∃ h', ptMap f W (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (f x) (f y) h' :=
  ⟨_, rfl⟩

private theorem ptMap_injective (f : L →+* K₀) (W : WeierstrassCurve L) :
    Function.Injective (ptMap f W) :=
  letI : Algebra L K₀ := f.toAlgebra
  WeierstrassCurve.Affine.Point.map_injective _

private theorem addOrderOf_ptMap (f : L →+* K₀) (W : WeierstrassCurve L) (P : W.toAffine.Point) :
    addOrderOf (ptMap f W P) = addOrderOf P :=
  addOrderOf_injective (ptMap f W) (ptMap_injective f W) P

private theorem coordsOrZero_ptMap (f : L →+* K₀) (W : WeierstrassCurve L) (P : W.toAffine.Point) :
    (ptMap f W P).coordsOrZero = (f P.coordsOrZero.1, f P.coordsOrZero.2) := by
  cases P with
  | zero =>
    have h0 : ptMap f W WeierstrassCurve.Affine.Point.zero =
        WeierstrassCurve.Affine.Point.zero := rfl
    rw [h0]
    simp
  | some x y h =>
    obtain ⟨h', hP⟩ := ptMap_some f W h
    rw [hP]
    rfl

omit [DecidableEq L] [DecidableEq K₀] in
private theorem map_b₂' (f : L →+* K₀) (W : WeierstrassCurve L) : (W.map f).b₂ = f W.b₂ := by
  show (f W.a₁) ^ 2 + 4 * f W.a₂ = f (W.a₁ ^ 2 + 4 * W.a₂)
  rw [map_add, map_mul, map_pow, map_ofNat]

omit [DecidableEq L] [DecidableEq K₀] in
private theorem map_veluGx (f : L →+* K₀) (W : WeierstrassCurve L) (x y : L) :
    (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [WeierstrassCurve.veluGx, map_sub, map_add, map_mul, map_pow, map_ofNat]
  rfl

omit [DecidableEq L] [DecidableEq K₀] in
private theorem map_veluGy (f : L →+* K₀) (W : WeierstrassCurve L) (x y : L) :
    (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [WeierstrassCurve.veluGy, map_neg, map_add, map_mul, map_ofNat]
  rfl

private theorem oddOrderSummingSet_ptMap (f : L →+* K₀) (W : WeierstrassCurve L)
    (P : W.toAffine.Point) (n : ℕ) :
    (W.map f).oddOrderSummingSet (ptMap f W P) n =
      (W.oddOrderSummingSet P n).image (fun p => (f p.1, f p.2)) := by
  rw [WeierstrassCurve.oddOrderSummingSet, WeierstrassCurve.oddOrderSummingSet,
    Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  show (k • ptMap f W P).coordsOrZero = (fun p => (f p.1, f p.2)) ((k • P).coordsOrZero)
  rw [← AddMonoidHom.map_nsmul, coordsOrZero_ptMap]

omit [DecidableEq L] [DecidableEq K₀] in
private theorem pairMap_injOn (f : L →+* K₀) (s : Finset (L × L)) :
    ∀ a ∈ s, ∀ b ∈ s, (fun p : L × L => (f p.1, f p.2)) a =
      (fun p : L × L => (f p.1, f p.2)) b → a = b := by
  intro a _ b _ hab
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext (f.injective hab.1) (f.injective hab.2)

private theorem map_sum_veluGx (f : L →+* K₀) (W : WeierstrassCurve L) (P : W.toAffine.Point) (n : ℕ) :
    ∑ p ∈ (W.map f).oddOrderSummingSet (ptMap f W P) n, (W.map f).veluGx p.1 p.2 =
      f (∑ p ∈ W.oddOrderSummingSet P n, W.veluGx p.1 p.2) := by
  rw [oddOrderSummingSet_ptMap, Finset.sum_image (pairMap_injOn f _), map_sum]
  exact Finset.sum_congr rfl fun p _ => map_veluGx f W p.1 p.2

private theorem map_sum_asym (f : L →+* K₀) (W : WeierstrassCurve L) (P : W.toAffine.Point) (n : ℕ) :
    ∑ p ∈ (W.map f).oddOrderSummingSet (ptMap f W P) n,
      (p.1 * (W.map f).veluGx p.1 p.2 - p.2 * (W.map f).veluGy p.1 p.2) =
      f (∑ p ∈ W.oddOrderSummingSet P n,
        (p.1 * W.veluGx p.1 p.2 - p.2 * W.veluGy p.1 p.2)) := by
  rw [oddOrderSummingSet_ptMap, Finset.sum_image (pairMap_injOn f _), map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sub, map_mul, map_mul, map_veluGx, map_veluGy]

private theorem fullKernelQuotient_map (f : L →+* K₀) (W : WeierstrassCurve L)
    (P : W.toAffine.Point) (N : ℕ) :
    (W.map f).fullKernelQuotient (ptMap f W P) N = (W.fullKernelQuotient P N).map f := by
  refine WeierstrassCurve.ext rfl rfl rfl ?_ ?_
  · show (W.map f).a₄ - 5 * _ = f (W.a₄ - 5 * _)
    rw [map_sum_veluGx f W P (N - 1), map_sub, map_mul, map_ofNat]
    rfl
  · show (W.map f).a₆ - (W.map f).b₂ * _ - 7 * _ = f (W.a₆ - W.b₂ * _ - 7 * _)
    rw [map_sum_veluGx f W P (N - 1), map_sum_asym f W P (N - 1), map_b₂', map_sub, map_sub,
      map_mul, map_mul, map_ofNat]
    rfl

end MapTransport

section TorsionSurj

variable {L K₀ : Type*} [Field L] [Field K₀] [DecidableEq L] [DecidableEq K₀]

omit [DecidableEq L] [DecidableEq K₀] in
private theorem mem_torsionBy_iff_nsmul {M : Type*} [AddCommGroup M] {n : ℕ} {x : M} :
    x ∈ Submodule.torsionBy ℤ M n ↔ n • x = 0 := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

private theorem ptMap_torsionBy_surj [IsAlgClosed L] [IsAlgClosed K₀] [CharZero L] [CharZero K₀]
    (f : L →+* K₀) (W : WeierstrassCurve L) [W.IsElliptic]
    {N : ℕ} (hN : N ≠ 0) (Q' : (W.map f).toAffine.Point) (hQ' : N • Q' = 0) :
    ∃ Q : W.toAffine.Point, N • Q = 0 ∧ ptMap f W Q = Q' := by
  haveI : (W.map f).IsElliptic := inferInstance
  set S := Submodule.torsionBy ℤ W.toAffine.Point N with hS
  set T := Submodule.torsionBy ℤ (W.map f).toAffine.Point N with hT
  have hcardS : Nat.card S = N ^ 2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W
      (by exact_mod_cast Nat.cast_ne_zero.mpr hN) two_ne_zero
  have hcardT : Nat.card T = N ^ 2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed (W.map f)
      (by exact_mod_cast Nat.cast_ne_zero.mpr hN) two_ne_zero
  haveI hfinS : Finite S := Nat.finite_of_card_ne_zero (by
    rw [hcardS]; exact pow_ne_zero 2 hN)
  haveI hfinT : Finite T := Nat.finite_of_card_ne_zero (by
    rw [hcardT]; exact pow_ne_zero 2 hN)

  set φ : S → T := fun x => ⟨ptMap f W x.1, mem_torsionBy_iff_nsmul.mpr (by
    rw [← AddMonoidHom.map_nsmul, mem_torsionBy_iff_nsmul.mp x.2]
    exact map_zero _)⟩ with hφ
  have hφinj : Function.Injective φ := fun a b hab => by
    apply Subtype.ext
    exact ptMap_injective f W (congrArg Subtype.val hab)
  have hφbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [hcardS, hcardT]⟩
  obtain ⟨⟨Q, hQmem⟩, hQeq⟩ := hφbij.2 ⟨Q', mem_torsionBy_iff_nsmul.mpr hQ'⟩
  exact ⟨Q, mem_torsionBy_iff_nsmul.mp hQmem, congrArg Subtype.val hQeq⟩

end TorsionSurj

section FibrePolyMap

private theorem map_eval₂RingHom_intCast {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Φ : Polynomial (Polynomial ℤ)) (a : R) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).map f =
      Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (f a)) := by
  rw [Polynomial.map_map]
  refine congrArg (fun (g : Polynomial ℤ →+* S) => Φ.map g) ?_
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

private theorem fibrePoly_map {k k' : Type*} [Field k] [Field k'] (f : k →+* k')
    (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    (fibrePoly Φ a).map f = fibrePoly Φ (f a) :=
  map_eval₂RingHom_intCast f Φ a

end FibrePolyMap

section Organ

namespace WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K]

private theorem nsmul_ne_zero_of_lt_addOrderOf {W : WeierstrassCurve K} (Q : W.toAffine.Point)
    {N : ℕ} (hQ : addOrderOf Q = N) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N - 1) :
    k • Q ≠ 0 := by
  intro h
  have hN : 1 ≤ N := le_trans hk1 (le_trans hkN (Nat.sub_le N 1))
  have hdvd : N ∣ k := hQ ▸ addOrderOf_dvd_of_nsmul_eq_zero h
  have hle : N ≤ k := Nat.le_of_dvd hk1 hdvd
  omega

private theorem hneg_oddOrderSummingSet (W : WeierstrassCurve K)
    {N : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    ∀ P ∈ W.oddOrderSummingSet Q (N - 1),
      (P.1, W.toAffine.negY P.1 P.2) ∈ W.oddOrderSummingSet Q (N - 1) := by
  intro P hP
  obtain ⟨k, hk1, hkN, hkP⟩ := (mem_oddOrderSummingSet W).mp hP
  have hN : 1 ≤ N := le_trans hk1 (le_trans hkN (Nat.sub_le N 1))
  refine (mem_oddOrderSummingSet W).mpr ⟨N - k, by omega, by omega, ?_⟩
  have hnk : (N - k) • Q = -(k • Q) := by
    have hsum : (N - k) • Q + k • Q = 0 := by
      rw [← add_nsmul, Nat.sub_add_cancel (by omega), ← hQ]
      exact addOrderOf_nsmul_eq_zero Q
    exact (neg_eq_of_add_eq_zero_left hsum).symm
  rw [hnk, coordsOrZero_neg _ (nsmul_ne_zero_of_lt_addOrderOf Q hQ hk1 hkN), hkP]

private theorem coordsOrZero_vcAddEquiv (C : VariableChange K) (W : WeierstrassCurve K)
    {P : W.toAffine.Point} (hP : P ≠ 0) :
    (ModularCurve.B3.vcAddEquiv C W P).coordsOrZero = vcInvEmbedding C P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

private theorem oddOrderSummingSet_vcAddEquiv (C : VariableChange K) (W : WeierstrassCurve K)
    {N : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (C • W).oddOrderSummingSet (ModularCurve.B3.vcAddEquiv C W Q) (N - 1) =
      (W.oddOrderSummingSet Q (N - 1)).map (vcInvEmbedding C) := by
  unfold oddOrderSummingSet
  rw [Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr ?_
  intro k hk
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk
  have hsm : k • (ModularCurve.B3.vcAddEquiv C W Q) = ModularCurve.B3.vcAddEquiv C W (k • Q) := by
    rw [← map_nsmul]
  simp only [Function.comp_apply, hsm]
  exact coordsOrZero_vcAddEquiv C W (nsmul_ne_zero_of_lt_addOrderOf Q hQ hk.1 hk.2)

private theorem variableChange_fullKernelQuotient (C : VariableChange K) (W : WeierstrassCurve K)
    {N : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (C • W).fullKernelQuotient (ModularCurve.B3.vcAddEquiv C W Q) N =
      C • (W.fullKernelQuotient Q N) := by
  unfold fullKernelQuotient
  rw [oddOrderSummingSet_vcAddEquiv C W Q hQ]
  exact variableChange_veluQuotientOfSums_asymWeights C W _ (hneg_oddOrderSummingSet W Q hQ)

end WeierstrassCurve

private theorem fullKernelQuotient_pointAddEquivOfEq {K : Type*} [Field K] [DecidableEq K]
    {W₁ W₂ : WeierstrassCurve K} (h : W₁ = W₂) (P : W₁.toAffine.Point) (N : ℕ) :
    W₂.fullKernelQuotient (ModularCurve.B3.pointAddEquivOfEq h P) N =
      W₁.fullKernelQuotient P N := by
  subst h
  rw [ModularCurve.B3.pointAddEquivOfEq_rfl]
  rfl

private theorem j_congr' {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} (h : W₁ = W₂)
    {i₁ : W₁.IsElliptic} {i₂ : W₂.IsElliptic} :
    @WeierstrassCurve.j K _ W₁ i₁ = @WeierstrassCurve.j K _ W₂ i₂ := by
  subst h
  rw [Subsingleton.elim i₁ i₂]

end Organ

section H0

open ModularCurve.TatePoint in

private theorem h0_of_transcendental {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀]
    [DecidableEq K₀] {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (W : WeierstrassCurve K₀) [W.IsElliptic] (hj : Transcendental ℚ W.j)
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K₀ _ (W.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  classical
  have hNne : N ≠ 0 := NeZero.ne N

  have hinjK : Function.Injective ⇑(Polynomial.aeval W.j : Polynomial ℚ →ₐ[ℚ] K₀) :=
    transcendental_iff_injective.mp hj
  set gK : Polynomial ℚ →+* K₀ := ↑(Polynomial.aeval W.j : Polynomial ℚ →ₐ[ℚ] K₀) with hgK
  have hinjK' : Function.Injective ⇑gK := hinjK
  set keyK : RatFunc ℚ →+* K₀ := IsFractionRing.lift hinjK' with hkeyK
  have htH : Transcendental ℚ (nearCurve (0 : Qbar)).j := by
    have h := nearCurve_j_transcendental 0
    rw [transcendental_iff_injective] at h ⊢
    have hcomp : ((Polynomial.aeval (nearCurve (0 : Qbar)).j : Polynomial ℚ →ₐ[ℚ] H) :
          Polynomial ℚ →+* H) =
        ((Polynomial.aeval (nearCurve (0 : Qbar)).j : Polynomial Qbar →ₐ[Qbar] H) :
            Polynomial Qbar →+* H).comp (Polynomial.mapRingHom (algebraMap ℚ Qbar)) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      simp
    intro a b hab
    have ha := congrArg (fun F : Polynomial ℚ →+* H => F a) hcomp
    have hb := congrArg (fun F : Polynomial ℚ →+* H => F b) hcomp
    simp only [RingHom.coe_coe, RingHom.comp_apply, Polynomial.coe_mapRingHom] at ha hb
    have hmap : (a.map (algebraMap ℚ Qbar)) = (b.map (algebraMap ℚ Qbar)) := by
      apply h
      rw [← ha, ← hb]
      exact hab
    exact Polynomial.map_injective _ (algebraMap ℚ Qbar).injective hmap
  have hinjH : Function.Injective
      ⇑(Polynomial.aeval (nearCurve (0 : Qbar)).j : Polynomial ℚ →ₐ[ℚ] H) :=
    transcendental_iff_injective.mp htH
  set gH : Polynomial ℚ →+* H :=
    ↑(Polynomial.aeval (nearCurve (0 : Qbar)).j : Polynomial ℚ →ₐ[ℚ] H) with hgH
  have hinjH' : Function.Injective ⇑gH := hinjH
  set keyH : RatFunc ℚ →+* H := IsFractionRing.lift hinjH' with hkeyH

  letI algK : Algebra (RatFunc ℚ) K₀ := keyK.toAlgebra
  letI algH : Algebra (RatFunc ℚ) H := keyH.toAlgebra
  set Lf := algebraicClosure (RatFunc ℚ) K₀ with hLfdef
  haveI hLalg : Algebra.IsAlgebraic (RatFunc ℚ) ↥Lf :=
    (algebraicClosure.isAlgClosure (RatFunc ℚ) K₀).isAlgebraic
  haveI hLclosed : IsAlgClosed ↥Lf :=
    (algebraicClosure.isAlgClosure (RatFunc ℚ) K₀).isAlgClosed
  haveI : CharZero ↥Lf := (algebraMap ↥Lf K₀).charZero

  set g : ↥Lf →ₐ[RatFunc ℚ] H := IsAlgClosed.lift with hgdef
  have hginj : Function.Injective ⇑g := g.toRingHom.injective

  have hkeyKX : keyK (algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X) = W.j := by
    rw [hkeyK, IsFractionRing.lift_algebraMap]
    show Polynomial.aeval W.j Polynomial.X = W.j
    exact Polynomial.aeval_X W.j
  have hWjmem : W.j ∈ Lf := by
    rw [← hkeyKX]
    exact Lf.algebraMap_mem _
  set tL : ↥Lf := ⟨W.j, hWjmem⟩ with htLdef
  set V : WeierstrassCurve ↥Lf := WeierstrassCurve.ofJ tL with hVdef
  haveI hVell : V.IsElliptic := by
    show (WeierstrassCurve.ofJ tL).IsElliptic
    infer_instance
  have hVj : V.j = tL := WeierstrassCurve.ofJ_j tL
  have htLcoe : algebraMap ↥Lf K₀ tL = W.j := rfl
  have hgtL : (g : ↥Lf →+* H) tL = (nearCurve (0 : Qbar)).j := by
    show g tL = _
    have h2 : tL = algebraMap (RatFunc ℚ) ↥Lf
        (algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X) := by
      apply Subtype.ext
      show W.j = _
      rw [← hkeyKX]
      exact IsScalarTower.algebraMap_apply (RatFunc ℚ) ↥Lf K₀ _
    rw [h2, g.commutes]
    show keyH _ = _
    rw [hkeyH, IsFractionRing.lift_algebraMap]
    show Polynomial.aeval (nearCurve (0 : Qbar)).j Polynomial.X = _
    exact Polynomial.aeval_X _

  set VH : WeierstrassCurve H := V.map (g : ↥Lf →+* H) with hVHdef
  haveI hVHell : VH.IsElliptic := by
    show (V.map (g : ↥Lf →+* H)).IsElliptic
    infer_instance
  have hVHj : Transcendental Qbar VH.j := by
    have hh : VH.j = (nearCurve (0 : Qbar)).j := by
      show (V.map (g : ↥Lf →+* H)).j = _
      rw [WeierstrassCurve.map_j, hVj, hgtL]
    rw [hh]
    exact nearCurve_j_transcendental 0

  set fK : ↥Lf →+* K₀ := algebraMap ↥Lf K₀ with hfKdef
  have hFj : (V.map fK).j = W.j := by
    rw [WeierstrassCurve.map_j, hVj]
    exact htLcoe
  obtain ⟨Cvc, hCvc⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (V.map fK) W hFj
  set e : (V.map fK).toAffine.Point ≃+ W.toAffine.Point :=
    (ModularCurve.B3.vcAddEquiv Cvc (V.map fK)).trans
      (ModularCurve.B3.pointAddEquivOfEq hCvc) with hedef
  set QvK : ι → (V.map fK).toAffine.Point := fun i => e.symm (Q i) with hQvKdef
  have hQvKord : ∀ i, addOrderOf (QvK i) = N := fun i =>
    (addOrderOf_injective e.symm.toAddMonoidHom e.symm.injective (Q i)).trans (hQ i)
  have hQvKtor : ∀ i, N • QvK i = 0 := fun i => by
    rw [← hQvKord i]
    exact addOrderOf_nsmul_eq_zero _
  choose QL hQLtor hQLmap using fun i => ptMap_torsionBy_surj fK V hNne (QvK i) (hQvKtor i)
  have hQLord : ∀ i, addOrderOf (QL i) = N := fun i => by
    rw [← addOrderOf_ptMap fK V (QL i), hQLmap]
    exact hQvKord i
  have hQLinj : Function.Injective fun i => AddSubgroup.zmultiples (QL i) := by
    intro i i' hii
    apply hQinj
    have h1 : AddSubgroup.zmultiples (QvK i) = AddSubgroup.zmultiples (QvK i') := by
      rw [← hQLmap i, ← hQLmap i', ← AddMonoidHom.map_zmultiples, ← AddMonoidHom.map_zmultiples]
      exact congrArg _ hii
    have h2 := congrArg (AddSubgroup.map e.toAddMonoidHom) h1
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples] at h2
    have h3 : e.toAddMonoidHom (QvK i) = Q i := e.apply_symm_apply (Q i)
    have h4 : e.toAddMonoidHom (QvK i') = Q i' := e.apply_symm_apply (Q i')
    rw [h3, h4] at h2
    exact h2

  have hquotK : ∀ i, W.fullKernelQuotient (Q i) N =
      Cvc • ((V.map fK).fullKernelQuotient (QvK i) N) := fun i => by
    have h1 : Q i = ModularCurve.B3.pointAddEquivOfEq hCvc
        (ModularCurve.B3.vcAddEquiv Cvc (V.map fK) (QvK i)) := by
      have := e.apply_symm_apply (Q i)
      rw [hedef] at this
      exact this.symm
    rw [h1, fullKernelQuotient_pointAddEquivOfEq hCvc,
      WeierstrassCurve.variableChange_fullKernelQuotient Cvc (V.map fK) (QvK i) (hQvKord i)]

  have hquotmap : ∀ i, (V.map fK).fullKernelQuotient (QvK i) N =
      (V.fullKernelQuotient (QL i) N).map fK := fun i => by
    rw [← hQLmap i]
    exact fullKernelQuotient_map fK V (QL i) N

  have hΔL : ∀ i, (V.fullKernelQuotient (QL i) N).Δ ≠ 0 := fun i => by
    intro h0
    apply hΔ i
    rw [hquotK i, WeierstrassCurve.variableChange_Δ, hquotmap i, WeierstrassCurve.map_Δ, h0,
      map_zero, mul_zero]

  set QH : ι → VH.toAffine.Point := fun i => ptMap (g : ↥Lf →+* H) V (QL i) with hQHdef
  have hQHord : ∀ i, addOrderOf (QH i) = N := fun i =>
    (addOrderOf_ptMap (g : ↥Lf →+* H) V (QL i)).trans (hQLord i)
  have hQHinj : Function.Injective fun i => AddSubgroup.zmultiples (QH i) := by
    intro i i' hii
    apply hQLinj
    have h1 : AddSubgroup.map (ptMap (g : ↥Lf →+* H) V) (AddSubgroup.zmultiples (QL i)) =
        AddSubgroup.map (ptMap (g : ↥Lf →+* H) V) (AddSubgroup.zmultiples (QL i')) := by
      rw [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples]
      exact hii
    exact AddSubgroup.map_injective (ptMap_injective (g : ↥Lf →+* H) V) h1
  have hΔH : ∀ i, (VH.fullKernelQuotient (QH i) N).Δ ≠ 0 := fun i => by
    have h1 : VH.fullKernelQuotient (QH i) N =
        (V.fullKernelQuotient (QL i) N).map (g : ↥Lf →+* H) :=
      fullKernelQuotient_map (g : ↥Lf →+* H) V (QL i) N
    rw [h1, WeierstrassCurve.map_Δ]
    intro h0
    exact hΔL i (hginj (h0.trans (map_zero _).symm))
  have hHid := fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental data VH hVHj hι QH
    hQHord hQHinj hΔH

  have hfKinj : Function.Injective ⇑fK := fK.injective
  have hLid : fibrePoly data.Φ V.j =
      ∏ i, (X - C (@WeierstrassCurve.j ↥Lf _ (V.fullKernelQuotient (QL i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔL i)⟩)) := by
    apply Polynomial.map_injective (g : ↥Lf →+* H) hginj
    rw [fibrePoly_map]
    have hgVj : (g : ↥Lf →+* H) V.j = VH.j := by
      rw [show VH.j = (V.map (g : ↥Lf →+* H)).j from rfl, WeierstrassCurve.map_j]
    rw [hgVj, hHid, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    haveI iL : (V.fullKernelQuotient (QL i) N).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (hΔL i)⟩
    have hjfac : (g : ↥Lf →+* H) (@WeierstrassCurve.j ↥Lf _ (V.fullKernelQuotient (QL i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔL i)⟩) =
        @WeierstrassCurve.j H _ (VH.fullKernelQuotient (QH i) N)
          ⟨isUnit_iff_ne_zero.mpr (hΔH i)⟩ := by
      rw [← WeierstrassCurve.map_j]
      exact j_congr' (fullKernelQuotient_map (g : ↥Lf →+* H) V (QL i) N).symm
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjfac]

  have hfinal := congrArg (Polynomial.map fK) hLid
  rw [fibrePoly_map, Polynomial.map_prod] at hfinal
  have hfKVj : fK V.j = W.j := by
    rw [hVj]
    exact htLcoe
  rw [hfKVj] at hfinal
  rw [hfinal]
  refine Finset.prod_congr rfl fun i _ => ?_
  haveI iL : (V.fullKernelQuotient (QL i) N).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (hΔL i)⟩
  have hΔK : ((V.map fK).fullKernelQuotient (QvK i) N).Δ ≠ 0 := by
    rw [hquotmap i, WeierstrassCurve.map_Δ]
    exact fun h0 => hΔL i (hfKinj (h0.trans (map_zero fK).symm))
  haveI iK : ((V.map fK).fullKernelQuotient (QvK i) N).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔK⟩
  have hjfac : fK (@WeierstrassCurve.j ↥Lf _ (V.fullKernelQuotient (QL i) N)
      ⟨isUnit_iff_ne_zero.mpr (hΔL i)⟩) =
      @WeierstrassCurve.j K₀ _ (W.fullKernelQuotient (Q i) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩ := by
    rw [← WeierstrassCurve.map_j]
    exact (j_congr' (hquotmap i).symm).trans
      (((WeierstrassCurve.variableChange_j _ _).symm).trans (j_congr' (hquotK i).symm))
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hjfac]

end H0
end ModularCurve.FKQTransport

theorem solution
    {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
    {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
    {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
    (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K₀ _
      (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) :=
  ModularCurve.FKQTransport.h0_of_transcendental data W _hj _hι Q _hQ _hQinj hΔ

end S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero (solution)
