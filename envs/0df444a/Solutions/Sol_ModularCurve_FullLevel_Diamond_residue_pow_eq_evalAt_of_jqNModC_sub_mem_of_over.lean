-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/dd8f25b4-cad5-5b41-a7df-640c21401aac

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace FrobPinSol

open Polynomial

theorem exists_intCast_eq_of_pow_eq {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {x : K} (hx : x ^ p = x) : ∃ n : ℤ, (n : K) = x :=
  (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr hx)

noncomputable def ev (S : Type*) [CommRing S] (a b : S) : Polynomial (Polynomial ℤ) →+* S :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom S) a) b

theorem ev_C_X (S : Type*) [CommRing S] (a b : S) : ev S a b (C X) = a := by
  simp [ev]

theorem ev_X (S : Type*) [CommRing S] (a b : S) : ev S a b X = b := by
  simp [ev]

theorem ev_map {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T) (a b : S)
    (Φ : Polynomial (Polynomial ℤ)) : g (ev S a b Φ) = ev T (g a) (g b) Φ := by
  have hinner : g.comp (Polynomial.eval₂RingHom (Int.castRingHom S) a) =
      Polynomial.eval₂RingHom (Int.castRingHom T) (g a) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  simp only [ev, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.hom_eval₂, hinner]

theorem ev_jq_eq (b : LaurentSeries ℚ) (Φ : Polynomial (Polynomial ℤ)) :
    ev (LaurentSeries ℚ) ModularCurve.jq b Φ = Φ.eval₂ ModularCurve.evalAtJ b := by
  have h : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) ModularCurve.jq =
      ModularCurve.evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [ModularCurve.evalAtJ_X]
  simp only [ev, Polynomial.coe_eval₂RingHom]
  rw [h]

theorem exists_kronecker_lift (q : ℕ) [Fact q.Prime] (data : ModularCurve.ModularPolynomialData q) :
    ∃ Ψ : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * Ψ := by
  have hK := ModularCurve.modularPolynomial_kronecker q data
  set P : Polynomial (Polynomial ℤ) := (C X ^ q - X) * (C X - X ^ q) with hP
  have hPmap : P.map (Polynomial.mapRingHom (Int.castRingHom (ZMod q))) =
      (C X ^ q - X) * (C X - X ^ q) := by
    simp [hP, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow]
  have hker : data.Φ - P ∈ RingHom.ker
      (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom (ZMod q)))) := by
    rw [RingHom.mem_ker, Polynomial.coe_mapRingHom, Polynomial.map_sub, hK, hPmap, sub_self]
  rw [Polynomial.ker_mapRingHom, Polynomial.ker_mapRingHom, ZMod.ker_intCastRingHom,
    Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hker
  obtain ⟨Ψ, hΨ⟩ := hker
  exact ⟨Ψ, by rw [← hΨ, hP]; ring⟩

theorem exists_ev_eq (q : ℕ) [Fact q.Prime] (data : ModularCurve.ModularPolynomialData q)
    (S : Type*) [CommRing S] (a b : S) :
    ∃ ψ : S, ev S a b data.Φ = (a ^ q - b) * (a - b ^ q) + (q : S) * ψ := by
  obtain ⟨Ψ, hΨ⟩ := exists_kronecker_lift q data
  refine ⟨ev S a b Ψ, ?_⟩
  conv_lhs => rw [hΨ]
  simp only [map_add, map_mul, map_sub, map_pow, ev_C_X, ev_X]
  congr 1
  simp [ev]

theorem core {R C κ : Type*} [CommRing R] [CommRing C] [Algebra R C] [Field κ]
    (q : ℕ) [hq : Fact q.Prime] [CharP κ q]
    (y : Ideal C) [y.IsPrime]
    (ρA : R →+* κ)
    (htransfer : ∀ r : R, algebraMap R C r ∈ y ↔ ρA r = 0)
    (t : κ) (ht : t ^ (q ^ 2) = t)
    (J jOf : C) (a₀ : R)
    (ha₀ : jOf - algebraMap R C a₀ ∈ y)
    (hkron : (J ^ q - jOf) * (J - jOf ^ q) ∈ y)
    (hover₀ : ∀ r : R, ρA r = t → J - algebraMap R C r ∈ y)
    (hover₁ : ∀ r : R, ρA r = t ^ (q + 1) → J ^ (q + 1) - algebraMap R C r ∈ y)
    (hover₂ : ∀ r : R, ρA r = t + t ^ q → J + J ^ q - algebraMap R C r ∈ y) :
    (ρA a₀) ^ q = t := by
  classical
  haveI : IsDomain (C ⧸ y) := Ideal.Quotient.isDomain y

  set ρC : R →+* C ⧸ y := (Ideal.Quotient.mk y).comp (algebraMap R C) with hρC
  have hρC0 : ∀ r : R, ρC r = 0 ↔ ρA r = 0 := fun r => by
    rw [hρC, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, htransfer]
  have htr : ∀ r r' : R, ρC r = ρC r' → ρA r = ρA r' := fun r r' h => by
    rw [← sub_eq_zero, ← map_sub] at h ⊢
    exact (hρC0 _).mp h

  have hqC : (q : C ⧸ y) = 0 := by
    have : ρC (q : R) = 0 := (hρC0 _).mpr (by rw [map_natCast]; exact CharP.cast_eq_zero κ q)
    rwa [map_natCast] at this
  haveI : CharP (C ⧸ y) q := (CharP.charP_iff_prime_eq_zero hq.out).mpr hqC

  have htq1 : (t ^ (q + 1)) ^ q = t ^ (q + 1) := by
    rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, ht, pow_succ']
  have htq2 : (t + t ^ q) ^ q = t + t ^ q := by
    rw [add_pow_char, ← pow_mul, ← sq, ht, add_comm]
  obtain ⟨n₁, hn₁⟩ := exists_intCast_eq_of_pow_eq q htq1
  obtain ⟨n₂, hn₂⟩ := exists_intCast_eq_of_pow_eq q htq2

  set β : C ⧸ y := Ideal.Quotient.mk y J with hβ
  set α : C ⧸ y := Ideal.Quotient.mk y jOf with hα
  have hαa : α = ρC a₀ := by
    rw [hα, hρC, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact ha₀
  have hN : β ^ (q + 1) = (n₁ : C ⧸ y) := by
    have h := hover₁ (n₁ : R) (by rw [map_intCast, hn₁])
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero] at h
    rw [hβ, h, ← RingHom.comp_apply, ← hρC, map_intCast]
  have hT : β + β ^ q = (n₂ : C ⧸ y) := by
    have h := hover₂ (n₂ : R) (by rw [map_intCast, hn₂])
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, map_pow, sub_eq_zero] at h
    rw [hβ, h, ← RingHom.comp_apply, ← hρC, map_intCast]
  have hβq : β ^ q = (n₂ : C ⧸ y) - β := by rw [← hT]; ring

  have hβqq : β ^ (q ^ 2) = β := by
    have hfix : ((n₂ : C ⧸ y)) ^ q = n₂ := by
      have := map_intCast (frobenius (C ⧸ y) q) n₂
      rwa [frobenius_def] at this
    rw [sq, pow_mul, hβq, sub_pow_char, hfix, hβq, sub_sub_cancel]

  have hK : α ^ q = β := by
    have h : (β ^ q - α) * (β - α ^ q) = 0 := by
      have := (Ideal.Quotient.eq_zero_iff_mem).mpr hkron
      simpa [hβ, hα, map_mul, map_sub, map_pow] using this
    rcases mul_eq_zero.mp h with h | h
    · rw [sub_eq_zero] at h
      rw [← h, ← pow_mul, ← sq, hβqq]
    · rw [sub_eq_zero] at h
      exact h.symm

  set X : κ := ρA a₀ ^ q with hX
  have hquadC : ρC (a₀ ^ q * a₀ ^ q - (n₂ : R) * a₀ ^ q + (n₁ : R)) = 0 := by
    have hb : ρC (a₀ ^ q) = β := by rw [map_pow, ← hαa, hK]
    simp only [map_add, map_sub, map_mul, map_intCast, hb]
    have h2 : β * β ^ q = (n₁ : C ⧸ y) := by rw [← hN]; ring
    rw [hβq] at h2
    linear_combination -h2
  have hquad : (X - t) * (X - t ^ q) = 0 := by
    have h := (hρC0 _).mp hquadC
    simp only [map_add, map_sub, map_mul, map_intCast, map_pow, hn₁, hn₂] at h
    rw [hX]
    linear_combination h
  rcases mul_eq_zero.mp hquad with h | h
  · exact sub_eq_zero.mp h
  ·
    have hXt : X = t ^ q := sub_eq_zero.mp h
    have hc : ρA (a₀ ^ (q ^ 2)) = t := by
      rw [map_pow, sq, pow_mul, ← hX, hXt, ← pow_mul, ← sq, ht]
    have h0 := hover₀ _ hc
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h0
    have h1 : ρC (a₀ ^ (q ^ 2)) = ρC (a₀ ^ q) := by
      rw [hρC, RingHom.comp_apply, RingHom.comp_apply, ← h0, ← hβ, ← hK, hαa, ← map_pow]
      rfl
    have h2 := htr _ _ h1
    rw [map_pow, map_pow, ← hX, sq, pow_mul, ← hX, hXt, ← pow_mul, ← sq, ht] at h2
    rw [hXt, ← h2]

section Constants

variable {L : Type*} [Field L] {k : Type*} [Field k] [Algebra k L]

noncomputable def toA (A : ValuationSubring L) : ↥(A.comap (algebraMap k L)) →+* ↥A :=
  (algebraMap k L).restrict (A.comap (algebraMap k L)).toSubring A.toSubring (fun _ hx => hx)

@[scoped simp] theorem coe_toA (A : ValuationSubring L) (r : ↥(A.comap (algebraMap k L))) :
    ((toA A r : ↥A) : L) = algebraMap k L (r : k) := rfl

theorem isUnit_of_isUnit_toA (A : ValuationSubring L) (r : ↥(A.comap (algebraMap k L)))
    (h : IsUnit (toA A r)) : IsUnit r := by
  have hr0 : (r : k) ≠ 0 := by
    rintro h0
    apply h.ne_zero
    exact Subtype.ext (by simp [h0])
  obtain ⟨u, hu⟩ := h
  have hz : (algebraMap k L (r : k)) * (((u⁻¹ : (↥A)ˣ) : ↥A) : L) = 1 := by
    have := congrArg (fun z : ↥A => (z : L)) u.mul_inv
    simpa [hu] using this
  have hinv : ((r : k)⁻¹) ∈ A.comap (algebraMap k L) := by
    show algebraMap k L (r : k)⁻¹ ∈ A
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hz]
    exact SetLike.coe_mem _
  exact IsUnit.of_mul_eq_one ⟨(r : k)⁻¹, hinv⟩ (Subtype.ext (by simp [mul_inv_cancel₀ hr0]))

theorem residue_toA_eq_zero_iff (A : ValuationSubring L) (r : ↥(A.comap (algebraMap k L))) :
    IsLocalRing.residue (↥A) (toA A r) = 0 ↔ r ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact ⟨isUnit_of_isUnit_toA A r, fun h => h.map _⟩

theorem algebraMap_mem_iff (A : ValuationSubring L) {C : Type*} [CommRing C]
    [Algebra (↥(A.comap (algebraMap k L))) C] (y : Ideal C) (hy : y ≠ ⊤)
    (π : ↥(A.comap (algebraMap k L)))
    (hunif : IsLocalRing.maximalIdeal (↥(A.comap (algebraMap k L))) = Ideal.span {π})
    (hπy : algebraMap _ C π ∈ y) (r : ↥(A.comap (algebraMap k L))) :
    algebraMap _ C r ∈ y ↔ IsLocalRing.residue (↥A) (toA A r) = 0 := by
  rw [residue_toA_eq_zero_iff]
  constructor
  · intro h
    by_contra hr
    have hu : IsUnit r := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
    exact hy (y.eq_top_of_isUnit_mem h (hu.map _))
  · intro h
    rw [hunif, Ideal.mem_span_singleton] at h
    obtain ⟨a, rfl⟩ := h
    rw [map_mul]
    exact y.mul_mem_right _ hπy

end Constants

section Eval

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_mul' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (mul_mem hf hg), ← map_mul]
  rfl

theorem evalAt_add' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (add_mem hf hg), ← map_add]
  rfl

theorem evalAt_pow' (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, evalAt_mul' v hv (pow_mem hf n) hf, ih, pow_succ]

theorem ord_nonneg_of_imp (P : Place K F) {f g : F}
    (hfg : f ∈ P.toValuationSubring → g ∈ P.toValuationSubring) (hf0 : f = 0 → g = 0)
    (h : 0 ≤ P.ord f) : 0 ≤ P.ord g := by
  by_cases hf : f = 0
  · rw [hf0 hf, Place.ord_zero]
  · exact P.ord_nonneg_of_mem (hfg (P.mem_of_ord_nonneg hf h))

end Eval

section QExp

p2m_open "ModularCurve~coeffEmb_qExpand"

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand (algebraMap ℚ L) n x

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L :=
  coeffMap_jqModC (algebraMap ℚ L)

theorem qExpand_coeffEmb_jq_mem (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    (hℓ : ℓ ∣ N) (H : Subgroup (ZMod N)ˣ) :
    qExpand L ℓ (coeffEmb L jq) ∈ laurentBaseChange L (xHFunctionField N H) := by
  rw [← coeffEmb_qExpand]
  refine coeffEmb_mem_laurentBaseChange L ?_
  have h1 : qExpand ℚ ℓ jq ∈ modularFunctionFieldFullC ℚ N := jqModCd_mem_full ℚ N hℓ
  exact x0_le_xHFunctionFieldC ℚ N H (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ N h1)

end QExp

end FrobPinSol
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over.FrobPinSol"

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 51200000

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_qExpand ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open FrobPinSol in
set_option linter.unusedVariables false in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y)

    (hover :
    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (hgK : (coeffEmb ↥k₀ g) ∈ K)
        (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ ∈ y))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ K)
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥K) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥K), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) a₀ ∈ y)
    :
    ∀ (hjR : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (ha₀ : ((a₀ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A),
      (residue A ⟨((a₀ : ↥k₀) : (AlgebraicClosure ℚ)), ha₀⟩) ^ q =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩) := by
  intro hjR ha₀
  classical

  haveI hprime : Fact q.Prime := inferInstance
  haveI : IsAlgClosed (ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP (ResidueField ↥A) q :=
    ValuationSubring.residueField_charP_of_liesOverPrime A hprime.out hA
  haveI := hy

  obtain ⟨hsrat, hsaff, hsss⟩ := (hW s).mp s.2
  have ht : (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
      (jGeomGen (ResidueField A) M') ^ (q ^ 2) =
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
      (jGeomGen (ResidueField A) M') :=
    pow_q_sq_eq_self_of_mem_ssJSet q hsss

  have hcoe : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [coeffMap_jqModC]; exact (coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm
  have hy1 : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hcoe]; exact coeffEmb_mem_laurentBaseChange _ (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨h1, h2⟩ := hR₀ (jqModC ↥A) hy1
  have key : ∀ (x x' : ↥(modularFunctionFieldBar M')) (hx : x ∈ R₀.integers) (hx' : x' ∈ R₀.integers),
      x = x' → R₀.residue ⟨x, hx⟩ = R₀.residue ⟨x', hx'⟩ := by
    intro x x' hx hx' h; subst h; rfl
  have hJres : R₀.residue ⟨_, hjR⟩ = jGeomGen (ResidueField A) M' := by
    rw [← key _ _ h1 hjR (Subtype.ext hcoe)]
    exact Subtype.ext (h2.trans (coeffMap_jqModC _))
  rw [hJres]

  have htransfer : ∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      algebraMap _ (↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) r ∈ y ↔
        ((IsLocalRing.residue ↥A).comp (toA A)) r = 0 :=
    fun r => algebraMap_mem_iff A y hy.ne_top ⟨π₀, hπ⟩ hunif hϖy r

  set ι : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* LaurentSeries ↥k₀ :=
    (K.val.toRingHom).comp (chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom
    with hιdef
  have hι : ∀ x, ι x = ((x : ↥K) : LaurentSeries ↥k₀) := fun x => rfl
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext (Subtype.ext h)
  have hJshK : coeffEmb ↥k₀ jq ∈ K := by rw [← hj]; exact j.2
  have hjeq : (⟨_, hJshK⟩ : ↥K) = j := Subtype.ext hj.symm
  have hJshC : (⟨_, hJshK⟩ : ↥K) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := by
    rw [hjeq]; exact subset_chartAlg _ _ {j} (Set.mem_singleton j)

  set JshC : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := ⟨⟨_, hJshK⟩, hJshC⟩
    with hJshCdef
  set jOfC : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :=
    ⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥K), hjC⟩ with hjOfCdef
  have hιJ : ι JshC = coeffEmb ↥k₀ jq := rfl
  have hιO : ι jOfC = jqNModC ↥k₀ q := rfl

  obtain ⟨data⟩ := nonempty_modularPolynomialData q
  have hΦ0 : ev _ JshC jOfC data.Φ = 0 := by
    apply hιinj
    rw [ev_map, map_zero, hιJ, hιO]
    have h0 := data.eval_eq_zero
    rw [← ev_jq_eq] at h0
    have h1 := congrArg (coeffEmb ↥k₀) h0
    rw [map_zero, ev_map] at h1
    have e2 : coeffEmb ↥k₀ (jqN q) = jqNModC ↥k₀ q := by
      rw [jqN, coeffEmb_qExpand, coeffEmb_jq, jqNModC]
    rw [e2] at h1
    exact h1
  have hkron : (JshC ^ q - jOfC) * (JshC - jOfC ^ q) ∈ y := by
    obtain ⟨ψ, hψ⟩ := exists_ev_eq q data _ JshC jOfC
    rw [hΦ0] at hψ
    have hq0 : (q : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) ∈ y := by
      have := (htransfer (q : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))).mpr
        (by rw [map_natCast]; exact CharP.cast_eq_zero _ q)
      rwa [map_natCast] at this
    have : (JshC ^ q - jOfC) * (JshC - jOfC ^ q) = -((q : _) * ψ) := by
      rw [eq_neg_iff_add_eq_zero]; exact hψ.symm
    rw [this]
    exact y.neg_mem (y.mul_mem_right _ hq0)

  have hjqF : jq ∈ modularFunctionFieldFull M' := modularFunctionField_le_full M' (jq_mem M')
  have hJreg : R₀.residue ⟨_, hjR⟩ ∈
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring := by
    rw [hJres]; exact hsaff.1

  have hres_a : ∀ (r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))),
      residue A ⟨((r : ↥k₀) : AlgebraicClosure ℚ), r.2⟩ = ((IsLocalRing.residue ↥A).comp (toA A)) r :=
    fun r => rfl

  have hover₀ : ∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      ((IsLocalRing.residue ↥A).comp (toA A)) r =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
          (jGeomGen (ResidueField A) M') →
      JshC - algebraMap _ _ r ∈ y := by
    intro r hr
    have H := hover jq hjqF hjR (fun P h => h) hJreg hJshK hJshC (r : ↥k₀) r.2
      (by rw [hres_a, hr, hJres])
    exact H

  have hover₁ : ∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      ((IsLocalRing.residue ↥A).comp (toA A)) r =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
          (jGeomGen (ResidueField A) M') ^ (q + 1) →
      JshC ^ (q + 1) - algebraMap _ _ r ∈ y := by
    intro r hr
    have hg : jq ^ (q + 1) ∈ modularFunctionFieldFull M' := pow_mem hjqF _
    have hel : (⟨coeffEmb (AlgebraicClosure ℚ) (jq ^ (q + 1)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) =
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) ^ (q + 1) := Subtype.ext (map_pow _ _ _)
    have hgi : (⟨coeffEmb (AlgebraicClosure ℚ) (jq ^ (q + 1)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈
        R₀.integers := by rw [hel]; exact pow_mem hjR _
    have hresg : R₀.residue ⟨_, hgi⟩ = (R₀.residue ⟨_, hjR⟩) ^ (q + 1) := by
      rw [← map_pow]
      exact congrArg R₀.residue (Subtype.ext (hel.trans (by simp)))
    have hgK : coeffEmb ↥k₀ (jq ^ (q + 1)) ∈ K := by
      rw [map_pow]; exact pow_mem hJshK _
    have helK : (⟨_, hgK⟩ : ↥K) = (⟨_, hJshK⟩ : ↥K) ^ (q + 1) := Subtype.ext (by simp [map_pow])
    have hgC : (⟨_, hgK⟩ : ↥K) ∈
        chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := by
      rw [helK]; exact pow_mem hJshC _
    have helC : (⟨⟨_, hgK⟩, hgC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) =
        JshC ^ (q + 1) := Subtype.ext (helK.trans (by simp [hJshCdef]))
    have H := hover (jq ^ (q + 1)) hg hgi
      (fun P h => ord_nonneg_of_imp P (fun hm => by rw [hel]; exact pow_mem hm _)
        (fun h0 => by rw [hel, h0, zero_pow (Nat.succ_ne_zero q)]) h)
      (by rw [hresg]; exact pow_mem hJreg _) hgK hgC (r : ↥k₀) r.2
      (by rw [hres_a, hr, hresg, hJres, evalAt_pow' _ hsrat hsaff.1])
    rwa [helC] at H

  have hover₂ : ∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      ((IsLocalRing.residue ↥A).comp (toA A)) r =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
          (jGeomGen (ResidueField A) M') +
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
          (jGeomGen (ResidueField A) M') ^ q →
      JshC + JshC ^ q - algebraMap _ _ r ∈ y := by
    intro r hr
    have hg : jq + jq ^ q ∈ modularFunctionFieldFull M' := add_mem hjqF (pow_mem hjqF _)
    have hel : (⟨coeffEmb (AlgebraicClosure ℚ) (jq + jq ^ q),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) =
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) +
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) ^ q := Subtype.ext (by simp [map_add, map_pow])
    have hgi : (⟨coeffEmb (AlgebraicClosure ℚ) (jq + jq ^ q),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈
        R₀.integers := by rw [hel]; exact add_mem hjR (pow_mem hjR _)
    have hresg : R₀.residue ⟨_, hgi⟩ = R₀.residue ⟨_, hjR⟩ + (R₀.residue ⟨_, hjR⟩) ^ q := by
      rw [← map_pow, ← map_add]
      exact congrArg R₀.residue (Subtype.ext (hel.trans (by simp)))
    have hgK : coeffEmb ↥k₀ (jq + jq ^ q) ∈ K := by
      rw [map_add, map_pow]; exact add_mem hJshK (pow_mem hJshK _)
    have helK : (⟨_, hgK⟩ : ↥K) = (⟨_, hJshK⟩ : ↥K) + (⟨_, hJshK⟩ : ↥K) ^ q :=
      Subtype.ext (by simp [map_add, map_pow])
    have hgC : (⟨_, hgK⟩ : ↥K) ∈
        chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := by
      rw [helK]; exact add_mem hJshC (pow_mem hJshC _)
    have helC : (⟨⟨_, hgK⟩, hgC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) =
        JshC + JshC ^ q := Subtype.ext (helK.trans (by simp [hJshCdef]))
    have H := hover (jq + jq ^ q) hg hgi
      (fun P h => ord_nonneg_of_imp P (fun hm => by rw [hel]; exact add_mem hm (pow_mem hm _))
        (fun h0 => by rw [hel, h0, zero_pow hprime.out.ne_zero, add_zero]) h)
      (by rw [hresg]; exact add_mem hJreg (pow_mem hJreg _)) hgK hgC (r : ↥k₀) r.2
      (by rw [hres_a, hr, hresg, hJres, evalAt_add' _ hsrat hsaff.1 (pow_mem hsaff.1 _),
            evalAt_pow' _ hsrat hsaff.1])
    rwa [helC] at H

  have hfinal := core q y ((IsLocalRing.residue ↥A).comp (toA A)) htransfer _ ht JshC jOfC a₀ ha₀y hkron
    hover₀ hover₁ hover₂
  rw [← hres_a] at hfinal
  exact hfinal

#print axioms solution

end S_ModularCurve_FullLevel_Diamond_residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_residue_pow_eq_evalAt_of_jqNModC_sub_mem_of_over (solution)
