-- Prove2me | solution 1 for ModularCurve.ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/19da651a-c2b3-5f31-a7c0-a4dfdb6a5ded

import Mathlib
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_level_mul_dedekindPsi_sub
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_three
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace IncP

p2m_open "ModularCurve~coeffMap_qExpand HahnSeries"

theorem ofPowerSeries_expand (R : Type) [CommRing R] (N : ℕ) [NeZero N] (u : PowerSeries R) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand N (NeZero.ne N) u) =
      qExpand R N (HahnSeries.ofPowerSeries ℤ R u) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul]
    rcases le_or_gt 0 m with hm | hm
    · lift m to ℕ using hm
      rw [show ((N : ℤ) * (m : ℤ)) = ((N * m : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_mul]
    · rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ (by
        have : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        nlinarith)]
  · rw [qExpand_coeff_of_not_dvd N _ hk]
    rcases le_or_gt 0 k with hk0 | hk0
    · lift k to ℕ using hk0 with n
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_expand_of_not_dvd]
      intro h; apply hk; exact_mod_cast h
    · rw [ofPowerSeries_coeff_of_neg _ hk0]

theorem coeffMap_ofPowerSeries {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_qExpand {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem jqModC_pow (K : Type) [CommRing K] (n : ℕ) :
    jqModC K ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

theorem jqNModC_eq (K : Type) [CommRing K] (N : ℕ) [NeZero N] :
    jqNModC K N = HahnSeries.single (-(N : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.expand N (NeZero.ne N) (jNum.map (Int.castRingHom K))) := by
  rw [jqNModC, jqModC, map_mul, qExpand_single, ofPowerSeries_expand]
  congr 1
  simp

theorem single_one_mul_single_one_neg (K : Type) [CommRing K] (k : ℤ) :
    (HahnSeries.single k (1 : K)) * HahnSeries.single (-k) 1 = 1 := by
  rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one]; rfl

theorem expand_jNum_eq_pow (κ : Type) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] [CharP κ ℓ] :
    PowerSeries.expand ℓ (Fact.out : ℓ.Prime).ne_zero (jNum.map (Int.castRingHom κ)) =
      (jNum.map (Int.castRingHom κ)) ^ ℓ := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have h := frobenius_identity_geom_unconditional κ (ℓ := ℓ)
  rw [jqNModC_eq, jqModC_pow] at h
  have h2 := congrArg (fun z => HahnSeries.single ((ℓ : ℤ)) (1 : κ) * z) h
  simp only [← mul_assoc] at h2
  rw [show ((ℓ : ℤ)) = -(-(ℓ : ℤ)) by ring, single_one_mul_single_one_neg, one_mul, one_mul] at h2
  have h3 := HahnSeries.ofPowerSeries_injective h2
  convert h3 using 2

theorem expand_sq_jNum_eq_pow (κ : Type) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] [CharP κ ℓ] :
    PowerSeries.expand (ℓ ^ 2) (pow_ne_zero 2 (Fact.out : ℓ.Prime).ne_zero) (jNum.map (Int.castRingHom κ)) =
      (jNum.map (Int.castRingHom κ)) ^ (ℓ ^ 2) := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have h1 := expand_jNum_eq_pow κ ℓ
  have : PowerSeries.expand (ℓ ^ 2) (pow_ne_zero 2 hℓ) (jNum.map (Int.castRingHom κ)) =
      PowerSeries.expand ℓ hℓ (PowerSeries.expand ℓ hℓ (jNum.map (Int.castRingHom κ))) := by
    rw [← PowerSeries.expand_mul ℓ hℓ ℓ hℓ]
    congr 1
    ring
  rw [this, h1, map_pow, h1, ← pow_mul, sq]

end IncP

namespace IncP

p2m_open "ModularCurve~coeffMap_qExpand HahnSeries AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel"

theorem eval₂_mul_inv_pow_mem {A F : Type} [CommRing A] [Field F] [Algebra A F] (x : F) (hx : x ≠ 0)
    (a : Polynomial ℤ) (D : ℕ) (hD : a.natDegree ≤ D) :
    Polynomial.eval₂ (Int.castRingHom F) x a * x⁻¹ ^ D ∈ Algebra.adjoin A ({x⁻¹} : Set F) := by
  have ha := a.as_sum_range_C_mul_X_pow
  rw [ha]
  rw [Polynomial.eval₂_finsetSum, Finset.sum_mul]
  refine Subalgebra.sum_mem _ (fun m hm => ?_)
  have hmD : m ≤ D := by
    have := Finset.mem_range.mp hm
    omega
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  have hxm : x ^ m * x⁻¹ ^ D = x⁻¹ ^ (D - m) := by
    rw [show D = m + (D - m) by omega, _root_.pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul,
      show m + (D - m) - m = D - m by omega]
  rw [mul_assoc, hxm, show (Int.castRingHom F) (a.coeff m) = algebraMap A F ((a.coeff m : ℤ) : A) by simp]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton A x⁻¹) _)

theorem inv_pow_mul_mem_chartAlgInf
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) (hj0 : j ≠ 0)
    (J : ↥K) (hJ : ((J : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.jqN N)) :
    (j⁻¹) ^ N * J ∈ chartAlgInf A (↥K) j := by
  classical

  set φj : Polynomial ℤ →+* ↥K := Polynomial.eval₂RingHom (Int.castRingHom ↥K) j with hφj
  have hroot : Polynomial.eval₂ φj J data.Φ = 0 := by
    apply Subtype.val_injective
    have h1 := Polynomial.hom_eval₂ data.Φ φj (algebraMap ↥K (LaurentSeries L)) J
    have hcomp : (algebraMap ↥K (LaurentSeries L)).comp φj =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) ((j : LaurentSeries L)) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [hφj]; simp
    have hcomp2 : (ModularCurve.coeffEmb L).comp ModularCurve.evalAtJ =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) ((j : LaurentSeries L)) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, ModularCurve.evalAtJ_X, ← hj]; simp
    have h2 := Polynomial.hom_eval₂ data.Φ ModularCurve.evalAtJ (ModularCurve.coeffEmb L) (ModularCurve.jqN N)
    rw [data.eval_eq_zero, map_zero, hcomp2, ← hJ] at h2
    show (algebraMap ↥K (LaurentSeries L)) (Polynomial.eval₂ φj J data.Φ) = ((0 : ↥K) : LaurentSeries L)
    rw [h1, hcomp]
    exact h2.symm.trans (by simp)

  set P : Polynomial ↥K := data.Φ.map φj with hP
  have hPm : P.Monic := data.monic.map φj
  have hPdeg : P.natDegree = dedekindPsi N := by rw [hP, data.monic.natDegree_map, data.natDegree_eq]
  have hPJ : Polynomial.aeval J P = 0 := by
    rw [Polynomial.coe_aeval_eq_eval, hP, Polynomial.eval_map]
    exact hroot
  set s : ↥K := (j⁻¹) ^ N with hs
  have hΨ0 : Polynomial.aeval (s * J) (P.scaleRoots s) = 0 := by
    have := Polynomial.scaleRoots_aeval_eq_zero (r := s) hPJ
    rwa [Algebra.algebraMap_self, RingHom.id_apply] at this
  have hΨm : (P.scaleRoots s).Monic := (Polynomial.monic_scaleRoots_iff s).mpr hPm

  have hcoef : ∀ i, (P.scaleRoots s).coeff i ∈ Algebra.adjoin A ({j⁻¹} : Set ↥K) := by
    intro i
    rw [Polynomial.coeff_scaleRoots, hPdeg, hP, Polynomial.coeff_map, hs, ← pow_mul, hφj,
      Polynomial.coe_eval₂RingHom]
    refine eval₂_mul_inv_pow_mem j hj0 _ _ ?_
    exact (ModularCurve.ModularPolynomialData.natDegree_coeff_le_level_mul_dedekindPsi_sub N data i).trans le_rfl

  have hlifts : P.scaleRoots s ∈ Polynomial.lifts (Algebra.adjoin A ({j⁻¹} : Set ↥K)).val.toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcoef i⟩, rfl⟩
  obtain ⟨Ψ₀, hΨ₀map, -, hΨ₀m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hΨm
  have hint : IsIntegral ↥(Algebra.adjoin A ({j⁻¹} : Set ↥K)) (s * J) := by
    refine ⟨Ψ₀, hΨ₀m, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map]
    show Polynomial.eval (s * J) (Ψ₀.map (Algebra.adjoin A ({j⁻¹} : Set ↥K)).val.toRingHom) = 0
    rw [hΨ₀map, ← Polynomial.coe_aeval_eq_eval]
    exact hΨ0
  exact (mem_chartAlg_iff A ↥K).mpr hint

end IncP

namespace IncP

p2m_open "ModularCurve~coeffMap_qExpand HahnSeries AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel"

theorem pow_ne_zero_of_constantCoeff_eq_one {R : Type} [CommRing R] [Nontrivial R] (u : PowerSeries R)
    (hu : PowerSeries.constantCoeff u = 1) (n : ℕ) : u ^ n ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [map_pow, hu, one_pow, map_zero] at this
  exact one_ne_zero this

theorem powerSeries_map_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (PowerSeries.map f) := by
  intro a b h
  ext n
  apply hf
  have := congrArg (PowerSeries.coeff n) h
  rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at this

theorem inv_mem_of_isUnit {F : Type} [Field F] (W : ValuationSubring F) (x : F) (hx : x ∈ W)
    (hu : IsUnit (⟨x, hx⟩ : ↥W)) : x ≠ 0 ∧ x⁻¹ ∈ W := by
  obtain ⟨u, hu⟩ := hu
  have hval : (((u⁻¹ : (↥W)ˣ) : ↥W) : F) * x = 1 := by
    have := congrArg (fun z : ↥W => (z : F)) u.inv_mul
    rw [hu] at this
    simpa using this
  have hx0 : x ≠ 0 := fun h => by rw [h, mul_zero] at hval; exact zero_ne_one hval
  refine ⟨hx0, ?_⟩
  have : x⁻¹ = (((u⁻¹ : (↥W)ˣ) : ↥W) : F) := (eq_inv_of_mul_eq_one_left hval).symm
  rw [this]; exact ((u⁻¹ : (↥W)ˣ) : ↥W).2

end IncP

p2m_open "ModularCurve~coeffMap_qExpand" in open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel HahnSeries in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]

    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (J₂ : ↥K) (hJ₂ : ((J₂ : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.jqN (q ^ 2)))
    (w : AlgebraicCurve.Place L ↥K)
    (hw : 0 < w.ord ((AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j :
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K))
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsMaximal]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y)
    (hwy : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), 0 < w.ord (b : ↥K) → b ∈ y) :
    w.ord J₂ = (q : ℤ) ^ 2 * w.ord (j : ↥K) := by
  classical
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 (Fact.out : q.Prime).ne_zero⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData (q ^ 2)
  have hj0 : j ≠ 0 := Fact.out

  have hgB : (j⁻¹) ^ (q ^ 2) * J₂ ∈ chartAlgInf A (↥K) j :=
    IncP.inv_pow_mul_mem_chartAlgInf (q ^ 2) data L K A j hj hj0 J₂ hJ₂
  set g : ↥K := (j⁻¹) ^ (q ^ 2) * J₂ with hg

  have hjinvw : (j⁻¹ : ↥K) ∈ w.toValuationSubring := by
    apply AlgebraicCurve.Place.mem_toValuationSubring_of_ord_nonneg
    have h := hw
    rw [coe_jInvChartInf] at h
    exact h.le
  have hconst : ∀ a : A, algebraMap A ↥K a ∈ w.toValuationSubring := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K]
    exact w.algebraMap_mem' _
  let Sw : Subalgebra A ↥K :=
    { carrier := w.toValuationSubring
      mul_mem' := fun ha hb => w.toValuationSubring.toSubring.mul_mem ha hb
      add_mem' := fun ha hb => w.toValuationSubring.toSubring.add_mem ha hb
      one_mem' := w.toValuationSubring.toSubring.one_mem
      zero_mem' := w.toValuationSubring.toSubring.zero_mem
      algebraMap_mem' := hconst }
  have hadjw : Algebra.adjoin A ({j⁻¹} : Set ↥K) ≤ Sw :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjinvw)
  have hBw : ∀ b : ↥K, b ∈ chartAlgInf A (↥K) j → b ∈ w.toValuationSubring := by
    intro b hb
    have hint : IsIntegral ↥(Algebra.adjoin A ({j⁻¹} : Set ↥K)) b := (mem_chartAlg_iff A ↥K).mp hb
    let ψ : ↥(Algebra.adjoin A ({j⁻¹} : Set ↥K)) →+* ↥w.toValuationSubring :=
      ((Algebra.adjoin A ({j⁻¹} : Set ↥K)).val.toRingHom).codRestrict w.toValuationSubring.toSubring
        (fun x => hadjw x.2)
    have hint' : IsIntegral ↥w.toValuationSubring b :=
      hint.map_of_comp_eq ψ (RingHom.id ↥K) (by ext x; rfl)
    obtain ⟨y', hy'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥w.toValuationSubring) (K := ↥K)).mp hint'
    rw [← hy']; exact y'.2
  have hOw : ∀ b : ↥K, b ∈ chartAlgInf A (↥K) j → 0 ≤ w.ord b := fun b hb =>
    AlgebraicCurve.Place.zero_le_ord_of_mem_toValuationSubring w (hBw b hb)

  set jA : PowerSeries A := jNum.map (Int.castRingHom A) with hjA
  set xA : PowerSeries A := PowerSeries.expand (q ^ 2) (NeZero.ne (q ^ 2)) jA with hxA
  set yA : PowerSeries A := jA ^ (q ^ 2) with hyA
  have hmapmap : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f₁ : R →+* S) (f₂ : S →+* T)
      (u : PowerSeries R), (u.map f₁).map f₂ = u.map (f₂.comp f₁) := by
    intro R S T _ _ _ f₁ f₂ u
    exact (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp f₁ f₂)) u).symm
  have hjL : jA.map (algebraMap A L) = jNum.map (Int.castRingHom L) := by
    rw [hjA, hmapmap, RingHom.ext_int ((algebraMap A L).comp (Int.castRingHom A)) (Int.castRingHom L)]
  have hjκ : jA.map (IsLocalRing.residue A) = jNum.map (Int.castRingHom (IsLocalRing.ResidueField A)) := by
    rw [hjA, hmapmap, RingHom.ext_int ((IsLocalRing.residue A).comp (Int.castRingHom A)) (Int.castRingHom _)]

  have hjLaurent : ((j : ↥K) : LaurentSeries L) = jqModC L := by
    rw [hj]; exact map_jqModC (algebraMap ℚ L)
  have hjpow : ((j : ↥K) : LaurentSeries L) ^ (q ^ 2) =
      HahnSeries.single (-((q ^ 2 : ℕ) : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)) := by
    rw [hjLaurent, IncP.jqModC_pow, ← hjL, ← map_pow (PowerSeries.map (algebraMap A L)), ← hyA]
  have hJLaurent : ((J₂ : ↥K) : LaurentSeries L) =
      HahnSeries.single (-((q ^ 2 : ℕ) : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ L (xA.map (algebraMap A L)) := by
    rw [hJ₂, ModularCurve.jqN, show ModularCurve.coeffEmb L (qExpand ℚ (q ^ 2) jq) =
        qExpand L (q ^ 2) (ModularCurve.coeffEmb L jq) from IncP.coeffMap_qExpand _ _ _,
      show ModularCurve.coeffEmb L jq = jqModC L from map_jqModC (algebraMap ℚ L)]
    rw [show qExpand L (q ^ 2) (jqModC L) = jqNModC L (q ^ 2) from rfl, IncP.jqNModC_eq, hxA,
      PowerSeries.map_expand, hjL]

  have hsingle0 : HahnSeries.single (-((q ^ 2 : ℕ) : ℤ)) (1 : L) ≠ 0 := by
    rw [Ne, HahnSeries.single_eq_zero_iff]; exact one_ne_zero
  have hy0L : HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)) ≠ 0 := by
    intro h
    apply hj0
    apply Subtype.ext
    have : ((j : ↥K) : LaurentSeries L) ^ (q ^ 2) = 0 := by rw [hjpow, h, mul_zero]
    exact pow_eq_zero_iff (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) |>.mp this
  have hgL : ((g : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)) =
      HahnSeries.ofPowerSeries ℤ L (xA.map (algebraMap A L)) := by
    have hjq0 : ((j : ↥K) : LaurentSeries L) ^ (q ^ 2) ≠ 0 := by rw [hjpow]; exact mul_ne_zero hsingle0 hy0L
    rw [hg]
    push_cast
    rw [hJLaurent, inv_pow, hjpow]
    calc (HahnSeries.single (-((q ^ 2 : ℕ) : ℤ)) (1 : L) * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)))⁻¹ *
          (HahnSeries.single (-((q ^ 2 : ℕ) : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ L (xA.map (algebraMap A L))) *
          HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L))
        = ((HahnSeries.single (-((q ^ 2 : ℕ) : ℤ)) (1 : L))⁻¹ * HahnSeries.single (-((q ^ 2 : ℕ) : ℤ)) 1) *
          (((HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)))⁻¹ * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L))) *
            HahnSeries.ofPowerSeries ℤ L (xA.map (algebraMap A L))) := by rw [mul_inv]; ring
      _ = HahnSeries.ofPowerSeries ℤ L (xA.map (algebraMap A L)) := by
          rw [inv_mul_cancel₀ hsingle0, inv_mul_cancel₀ hy0L, one_mul, one_mul]
  have hgm1L : (((g - 1 : ↥K)) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)) =
      HahnSeries.ofPowerSeries ℤ L ((xA - yA).map (algebraMap A L)) := by
    push_cast
    rw [sub_mul, hgL, one_mul, map_sub, map_sub]

  haveI : CharP (IsLocalRing.ResidueField A) q := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A q hAq
  have hjκ1 : PowerSeries.constantCoeff (jA.map (IsLocalRing.residue A)) = 1 := by
    rw [hjκ, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_jNum, map_one]
  have hybar : yA.map (IsLocalRing.residue A) ≠ 0 := by
    rw [hyA, map_pow]
    exact IncP.pow_ne_zero_of_constantCoeff_eq_one _ hjκ1 _
  have hxbar : xA.map (IsLocalRing.residue A) = yA.map (IsLocalRing.residue A) := by
    rw [hxA, hyA, PowerSeries.map_expand, map_pow, hjκ]
    exact IncP.expand_sq_jNum_eq_pow (IsLocalRing.ResidueField A) q

  have hgW : g ∈ W₀ := (hW₀ g).mpr ⟨xA, yA, hybar, hgL⟩
  have hgm1W : g - 1 ∈ W₀ := (hW₀ (g - 1)).mpr ⟨xA - yA, yA, hybar, hgm1L⟩
  have hgm1N : ((g - 1 : ↥K)) ∈ W₀.nonunits := by
    rw [show (g - 1 : ↥K) = ((⟨g - 1, hgm1W⟩ : ↥W₀) : ↥K) from rfl, ValuationSubring.coe_mem_nonunits_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨hne, hinv⟩ := IncP.inv_mem_of_isUnit W₀ _ hgm1W hu
    obtain ⟨x', y', hy', hEq⟩ := (hW₀ _).mp hinv

    have hEq2 : HahnSeries.ofPowerSeries ℤ L ((y' * yA).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (((xA - yA) * x').map (algebraMap A L)) := by
      rw [map_mul, map_mul, map_mul, map_mul, ← hgm1L]
      set G : LaurentSeries L := (((g - 1 : ↥K)) : LaurentSeries L) with hG
      have hne' : G ≠ 0 := by
        intro h; apply hne; exact Subtype.ext (by rw [hG] at h; simpa using h)
      have hEq' : G⁻¹ * HahnSeries.ofPowerSeries ℤ L (y'.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) := by
        rw [hG, ← hEq]; push_cast; rfl
      calc HahnSeries.ofPowerSeries ℤ L (y'.map (algebraMap A L)) * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L))
          = (G * G⁻¹) * HahnSeries.ofPowerSeries ℤ L (y'.map (algebraMap A L)) *
              HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)) := by
                rw [mul_inv_cancel₀ hne', one_mul]
        _ = G * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)) *
              (G⁻¹ * HahnSeries.ofPowerSeries ℤ L (y'.map (algebraMap A L))) := by ring
        _ = G * HahnSeries.ofPowerSeries ℤ L (yA.map (algebraMap A L)) *
              HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) := by rw [hEq']
    have hEq3 : y' * yA = (xA - yA) * x' :=
      IncP.powerSeries_map_injective (algebraMap A L) (IsFractionRing.injective A L)
        (HahnSeries.ofPowerSeries_injective hEq2)
    have hEq4 := congrArg (PowerSeries.map (IsLocalRing.residue A)) hEq3
    rw [map_mul, map_mul, map_sub, hxbar, sub_self, zero_mul] at hEq4
    exact (mul_ne_zero hy' hybar) hEq4

  have hg1y : (⟨g - 1, Subalgebra.sub_mem _ hgB (Subalgebra.one_mem _)⟩ : ↥(chartAlgInf A (↥K) j)) ∈ y :=
    hz₀ _ hgm1N
  have hordg : w.ord g = 0 := by
    rcases (hOw g hgB).lt_or_eq with hlt | heq
    · exfalso
      have hgy : (⟨g, hgB⟩ : ↥(chartAlgInf A (↥K) j)) ∈ y := hwy _ hlt
      apply (Ideal.IsMaximal.ne_top ‹y.IsMaximal›)
      rw [Ideal.eq_top_iff_one]
      have : (1 : ↥(chartAlgInf A (↥K) j)) = ⟨g, hgB⟩ - ⟨g - 1, Subalgebra.sub_mem _ hgB (Subalgebra.one_mem _)⟩ :=
        Subtype.ext (by simp)
      rw [this]
      exact y.sub_mem hgy hg1y
    · exact heq.symm

  have hx0L : HahnSeries.ofPowerSeries ℤ L (xA.map (algebraMap A L)) ≠ 0 := by
    intro h
    have h1 : xA.map (algebraMap A L) = 0 := HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
    have h2 := congrArg PowerSeries.constantCoeff h1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, hxA,
      PowerSeries.constantCoeff_expand, hjA, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum] at h2
    simp at h2
  have hJ0 : J₂ ≠ 0 := by
    intro h
    have h1 : ((J₂ : ↥K) : LaurentSeries L) = 0 := by rw [h]; rfl
    rw [hJLaurent] at h1
    exact (mul_ne_zero hsingle0 hx0L) h1
  have hordpow : ∀ n : ℕ, w.ord ((j⁻¹ : ↥K) ^ n) = (n : ℤ) * w.ord (j⁻¹ : ↥K) := by
    intro n
    rw [← zpow_natCast]
    exact w.ord_zpow _ _
  rw [hg, w.ord_mul (pow_ne_zero _ (inv_ne_zero hj0)) hJ0, hordpow, w.ord_inv] at hordg
  push_cast at hordg
  linarith

end S_ModularCurve_ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_three
end P2MW
export P2MW.S_ModularCurve_ord_jqN_sq_eq_sq_mul_ord_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_three (solution)
