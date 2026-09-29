-- Prove2me | solution 1 for ModularCurve.LevelComponent.exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8c4d92c5-938d-5d52-bcbc-80fc5fcbb59f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring
import Theorems.Thm_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_left
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open ModularCurve

namespace P2M
namespace RelWeilZar

open WeierstrassCurve MvPolynomial

section Field

noncomputable def V (ℓ : ℕ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω)
    (hW : IsUnit W.Δ) (D : LevelPData Ω) : Ω :=
  letI : W.IsElliptic := ⟨hW⟩
  ((WeierstrassCurve.Affine.weilPairing0 W Ω (ℓ : ℤ)
      (LevelRelabelling.toPoint (W.baseChange Ω) D.xP D.yP)
      (LevelRelabelling.toPoint (W.baseChange Ω) D.xQ D.yQ) : Ωˣ) : Ω)

theorem V_congr {ℓ : ℕ} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (i₁ i₂ : DecidableEq Ω) {W W' : WeierstrassCurve Ω}
    (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) {D D' : LevelPData Ω} (h1 : W = W') (h2 : D = D') :
    @V ℓ Ω _ _ i₁ W hW D = @V ℓ Ω _ _ i₂ W' hW' D' := by
  subst h1; subst h2
  have : i₁ = i₂ := Subsingleton.elim _ _
  subst this
  rfl

theorem V_eq_some {ℓ : ℕ} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω)
    [hE : W.IsElliptic] (D : LevelPData Ω)
    (hP : (W.baseChange Ω).toAffine.Nonsingular D.xP D.yP) (hQ : (W.baseChange Ω).toAffine.Nonsingular D.xQ D.yQ) :
    V ℓ Ω W hE.isUnit D = ((WeierstrassCurve.Affine.weilPairing0 W Ω (ℓ : ℤ)
      (WeierstrassCurve.Affine.Point.some _ _ hP) (WeierstrassCurve.Affine.Point.some _ _ hQ) : Ωˣ) : Ω) := by
  unfold V LevelRelabelling.toPoint
  rw [dif_pos hP, dif_pos hQ]

scoped instance isElliptic_baseChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  show (W.map (algebraMap R A)).IsElliptic from inferInstance

variable {F : Type u} [Field F] (W : WeierstrassCurve F) {ℓ : ℕ}

theorem nonsingular_P [W.IsElliptic] {D : LevelPData F} (hD : IsLevelPStructure W ℓ D) :
    (W.baseChange F).toAffine.Nonsingular D.xP D.yP :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (hD.equation_P.map (algebraMap F F))

theorem nonsingular_Q [W.IsElliptic] {D : LevelPData F} (hD : IsLevelPStructure W ℓ D) :
    (W.baseChange F).toAffine.Nonsingular D.xQ D.yQ :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (hD.equation_Q.map (algebraMap F F))

theorem zsmul_some_eq_zero [W.IsElliptic] [DecidableEq F] [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) {x y : F}
    (h : (W.baseChange F).toAffine.Nonsingular x y) (hx : (W.preΨ ℓ).eval x = 0) :
    (ℓ : ℤ) • WeierstrassCurve.Affine.Point.some _ _ h = 0 := by
  have hodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  rw [natCast_zsmul, WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi (W.baseChange F) hodd h]
  have hbc : W.baseChange F = W := W.map_id
  rw [hbc, ← WeierstrassCurve.preΨ_ofNat]
  exact hx

theorem V_pow_eq_one [DecidableEq F] [IsAlgClosed F] [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓF : (ℓ : F) ≠ 0)
    {D : LevelPData F} (hD : IsLevelPStructure W ℓ D) (hW : IsUnit W.Δ) :
    V ℓ F W hW D ^ ℓ = 1 := by
  haveI : W.IsElliptic := ⟨hW⟩
  have hP := nonsingular_P W hD
  have hQ := nonsingular_Q W hD
  rw [V_eq_some W D hP hQ, ← Units.val_pow_eq_pow_val, ← Units.val_one]
  congr 1
  haveI := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange F)
  set P := WeierstrassCurve.Affine.Point.some _ _ hP
  set Q := WeierstrassCurve.Affine.Point.some _ _ hQ
  have hPℓ : (ℓ : ℤ) • P = 0 := zsmul_some_eq_zero W hℓ2 hP hD.preΨ_P
  have hQℓ : (ℓ : ℤ) • Q = 0 := zsmul_some_eq_zero W hℓ2 hQ hD.preΨ_Q
  have h0 : WeierstrassCurve.Affine.weilPairing0 W F ℓ 0 Q = 1 := by
    have := WeierstrassCurve.Affine.weilPairing0_add_left W hℓF 0 0 Q (smul_zero _) (smul_zero _) hQℓ
    rw [add_zero] at this
    exact mul_eq_right.mp this.symm
  have hk : ∀ k : ℕ, WeierstrassCurve.Affine.weilPairing0 W F ℓ ((k : ℤ) • P) Q =
      WeierstrassCurve.Affine.weilPairing0 W F ℓ P Q ^ k := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, h0]
    | succ k ih =>
      have hkP : (ℓ : ℤ) • ((k : ℤ) • P) = 0 := by rw [smul_smul, mul_comm, ← smul_smul, hPℓ, smul_zero]
      rw [Nat.cast_succ, add_smul, one_smul,
        WeierstrassCurve.Affine.weilPairing0_add_left W hℓF _ _ Q hkP hPℓ hQℓ, ih, pow_succ]
  rw [← hk ℓ, hPℓ, h0]

end Field

section Universal

scoped instance : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm

abbrev Pu : Type u := MvPolynomial (Fin 9) (ULift.{u} ℤ)

noncomputable def W₀ : WeierstrassCurve Pu.{u} := ⟨X 0, X 1, X 2, X 3, X 4⟩

noncomputable def D₀ : LevelPData Pu.{u} := ⟨X 5, X 6, X 7, X 8⟩

noncomputable def g₀ (ℓ : ℕ) : Pu.{u} :=
  (ℓ : Pu.{u}) * W₀.Δ * indepElt W₀ ℓ (X 5) (X 7) * indepElt W₀ ℓ (X 7) (X 5)

abbrev Pg (ℓ : ℕ) : Type u := Localization.Away (g₀.{u} ℓ)

noncomputable def I₀ (ℓ : ℕ) : Ideal (Pg.{u} ℓ) :=
  Ideal.span {algebraMap Pu.{u} (Pg ℓ) (W₀.toAffine.polynomial.evalEval (X 5) (X 6)),
    algebraMap Pu.{u} (Pg ℓ) (W₀.toAffine.polynomial.evalEval (X 7) (X 8)),
    algebraMap Pu.{u} (Pg ℓ) ((W₀.preΨ ℓ).eval (X 5)),
    algebraMap Pu.{u} (Pg ℓ) ((W₀.preΨ ℓ).eval (X 7))}

abbrev Ru (ℓ : ℕ) : Type u := Pg.{u} ℓ ⧸ I₀ ℓ

noncomputable def π (ℓ : ℕ) : Pu.{u} →+* Ru ℓ := (Ideal.Quotient.mk (I₀ ℓ)).comp (algebraMap Pu.{u} (Pg ℓ))

noncomputable def Wu (ℓ : ℕ) : WeierstrassCurve (Ru.{u} ℓ) := W₀.map (π ℓ)

noncomputable def Du (ℓ : ℕ) : LevelPData (Ru.{u} ℓ) := D₀.map (π ℓ)

variable (ℓ : ℕ)

theorem isUnit_π_g₀ : IsUnit (π.{u} ℓ (g₀ ℓ)) := by
  rw [π, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Pg ℓ) (g₀.{u} ℓ)).map _

theorem isUnit_natCast_Ru : IsUnit ((ℓ : ℕ) : Ru.{u} ℓ) := by
  have h := isUnit_π_g₀.{u} ℓ
  simp only [g₀, map_mul, map_natCast] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h))

theorem isUnit_Δ_Wu : IsUnit (Wu.{u} ℓ).Δ := by
  have h := isUnit_π_g₀.{u} ℓ
  simp only [g₀, map_mul] at h
  rw [Wu, WeierstrassCurve.map_Δ]
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h))

theorem π_mem_eq_zero {p : Pu.{u}} (hp : algebraMap Pu.{u} (Pg ℓ) p ∈ I₀ ℓ) : π ℓ p = 0 := by
  rw [π, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact hp

theorem isLevelPStructure_Wu : IsLevelPStructure (Wu.{u} ℓ) ℓ (Du ℓ) where
  equation_P := by
    have h1 : (Du.{u} ℓ).xP = π ℓ (X 5) := rfl
    have h2 : (Du.{u} ℓ).yP = π ℓ (X 6) := rfl
    rw [WeierstrassCurve.Affine.Equation, h1, h2, Wu, WeierstrassCurve.Affine.map_polynomial,
      Polynomial.map_mapRingHom_evalEval]
    exact π_mem_eq_zero ℓ (Ideal.subset_span (Set.mem_insert _ _))
  equation_Q := by
    have h1 : (Du.{u} ℓ).xQ = π ℓ (X 7) := rfl
    have h2 : (Du.{u} ℓ).yQ = π ℓ (X 8) := rfl
    rw [WeierstrassCurve.Affine.Equation, h1, h2, Wu, WeierstrassCurve.Affine.map_polynomial,
      Polynomial.map_mapRingHom_evalEval]
    exact π_mem_eq_zero ℓ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  preΨ_P := by
    have h1 : (Du.{u} ℓ).xP = π ℓ (X 5) := rfl
    rw [h1, Wu, WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact π_mem_eq_zero ℓ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  preΨ_Q := by
    have h1 : (Du.{u} ℓ).xQ = π ℓ (X 7) := rfl
    rw [h1, Wu, WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact π_mem_eq_zero ℓ (Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
  isUnit_indepElt_PQ := by
    have h1 : (Du.{u} ℓ).xP = π ℓ (X 5) := rfl
    have h2 : (Du.{u} ℓ).xQ = π ℓ (X 7) := rfl
    rw [h1, h2, Wu, indepElt_map]
    have h := isUnit_π_g₀.{u} ℓ
    simp only [g₀, map_mul] at h
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)
  isUnit_indepElt_QP := by
    have h1 : (Du.{u} ℓ).xP = π ℓ (X 5) := rfl
    have h2 : (Du.{u} ℓ).xQ = π ℓ (X 7) := rfl
    rw [h1, h2, Wu, indepElt_map]
    have h := isUnit_π_g₀.{u} ℓ
    simp only [g₀, map_mul] at h
    exact isUnit_of_mul_isUnit_right h

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (D : LevelPData B)

noncomputable def ev : Pu.{u} →+* B :=
  MvPolynomial.eval₂Hom ((Int.castRingHom B).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)
    ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆, D.xP, D.yP, D.xQ, D.yQ]

theorem ev_X (i : Fin 9) : ev W D (X i) = ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆, D.xP, D.yP, D.xQ, D.yQ] i :=
  MvPolynomial.eval₂Hom_X' _ _ i

theorem map_W₀_ev : W₀.map (ev W D) = W := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · show ev W D (X 0) = W.a₁; rw [ev_X]; rfl
  · show ev W D (X 1) = W.a₂; rw [ev_X]; rfl
  · show ev W D (X 2) = W.a₃; rw [ev_X]; rfl
  · show ev W D (X 3) = W.a₄; rw [ev_X]; rfl
  · show ev W D (X 4) = W.a₆; rw [ev_X]; rfl

theorem ev_X5 : ev W D (X 5) = D.xP := by rw [ev_X]; rfl
theorem ev_X6 : ev W D (X 6) = D.yP := by rw [ev_X]; rfl
theorem ev_X7 : ev W D (X 7) = D.xQ := by rw [ev_X]; rfl
theorem ev_X8 : ev W D (X 8) = D.yQ := by rw [ev_X]; rfl

theorem map_D₀_ev : D₀.map (ev W D) = D := by
  refine LevelPData.ext ?_ ?_ ?_ ?_
  · show ev W D (X 5) = D.xP; exact ev_X5 W D
  · show ev W D (X 6) = D.yP; exact ev_X6 W D
  · show ev W D (X 7) = D.xQ; exact ev_X7 W D
  · show ev W D (X 8) = D.yQ; exact ev_X8 W D

variable {W D}

theorem isUnit_ev_g₀ (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) :
    IsUnit (ev W D (g₀ ℓ)) := by
  simp only [g₀, map_mul, map_natCast]
  refine ((hℓ.mul ?_).mul ?_).mul ?_
  · rw [← WeierstrassCurve.map_Δ, map_W₀_ev]; exact hΔ
  · rw [← indepElt_map, map_W₀_ev, ev_X5, ev_X7]; exact hD.isUnit_indepElt_PQ
  · rw [← indepElt_map, map_W₀_ev, ev_X5, ev_X7]; exact hD.isUnit_indepElt_QP

noncomputable def ev₁ (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) : Pg.{u} ℓ →+* B :=
  IsLocalization.Away.lift (g₀.{u} ℓ) (isUnit_ev_g₀ ℓ hD hΔ hℓ)

theorem ev₁_algebraMap (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) (p : Pu.{u}) :
    ev₁ ℓ hD hΔ hℓ (algebraMap Pu.{u} (Pg ℓ) p) = ev W D p :=
  IsLocalization.Away.lift_eq _ _ _

theorem I₀_le_ker (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) :
    I₀ ℓ ≤ RingHom.ker (ev₁ ℓ hD hΔ hℓ) := by
  rw [I₀, Ideal.span_le]
  have hW := map_W₀_ev W D
  rintro _ (rfl | rfl | rfl | rfl)
  all_goals rw [SetLike.mem_coe, RingHom.mem_ker, ev₁_algebraMap]
  · rw [← Polynomial.map_mapRingHom_evalEval, ← WeierstrassCurve.Affine.map_polynomial, ev_X5, ev_X6]
    have h := hD.equation_P
    rw [← hW] at h
    exact h
  · rw [← Polynomial.map_mapRingHom_evalEval, ← WeierstrassCurve.Affine.map_polynomial, ev_X7, ev_X8]
    have h := hD.equation_Q
    rw [← hW] at h
    exact h
  · rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_preΨ, hW, ev_X5]
    exact hD.preΨ_P
  · rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_preΨ, hW, ev_X7]
    exact hD.preΨ_Q

noncomputable def χ (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) : Ru.{u} ℓ →+* B :=
  Ideal.Quotient.lift (I₀ ℓ) (ev₁ ℓ hD hΔ hℓ) fun _ ha => I₀_le_ker ℓ hD hΔ hℓ ha

theorem χ_comp_π (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) :
    (χ ℓ hD hΔ hℓ).comp (π ℓ) = ev W D :=
  RingHom.ext fun p => by
    show χ ℓ hD hΔ hℓ (Ideal.Quotient.mk (I₀ ℓ) (algebraMap _ _ p)) = ev W D p
    rw [χ, Ideal.Quotient.lift_mk, ev₁_algebraMap]

theorem map_Wu_χ (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) :
    (Wu ℓ).map (χ ℓ hD hΔ hℓ) = W := by
  rw [Wu, WeierstrassCurve.map_map, χ_comp_π, map_W₀_ev]

theorem map_Du_χ (hD : IsLevelPStructure W ℓ D) (hΔ : IsUnit W.Δ) (hℓ : IsUnit ((ℓ : ℕ) : B)) :
    (Du ℓ).map (χ ℓ hD hΔ hℓ) = D := by
  rw [Du, LevelPData.map_map, χ_comp_π, map_D₀_ev]

end Universal

section Rule

variable (ℓ : ℕ)

theorem isUnit_Δ_map_Wu {Ω : Type u} [CommRing Ω] (φ : Ru.{u} ℓ →+* Ω) : IsUnit ((Wu ℓ).map φ).Δ := by
  rw [WeierstrassCurve.map_Δ]; exact (isUnit_Δ_Wu ℓ).map φ

noncomputable def cU (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : Ru.{u} ℓ →+* Ω) : Ω :=
  @V ℓ Ω _ _ (Classical.decEq Ω) ((Wu ℓ).map φ) (isUnit_Δ_map_Wu ℓ φ) ((Du ℓ).map φ)

theorem natCast_ne_zero_of_ringHom {Ω : Type u} [Field Ω] (φ : Ru.{u} ℓ →+* Ω) : ((ℓ : ℕ) : Ω) ≠ 0 := by
  simpa using ((isUnit_natCast_Ru ℓ).map φ).ne_zero

variable [Fact ℓ.Prime]

theorem cU_pow (hℓ2 : ℓ ≠ 2) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : Ru.{u} ℓ →+* Ω) : cU ℓ Ω φ ^ ℓ = 1 := by
  letI := Classical.decEq Ω
  exact V_pow_eq_one ((Wu ℓ).map φ) hℓ2 (natCast_ne_zero_of_ringHom ℓ φ) ((isLevelPStructure_Wu ℓ).map φ) _

theorem cU_val (hℓ2 : ℓ ≠ 2) (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : Ru.{u} ℓ →+* 𝒪) (ψ : 𝒪 →+* Ω) :
    ∃ u : 𝒪, cU ℓ K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ cU ℓ Ω (ψ.comp ρ) = ψ u := by
  letI := Classical.decEq K
  letI := Classical.decEq Ω
  haveI : (Wu.{u} ℓ).IsElliptic := ⟨isUnit_Δ_Wu ℓ⟩
  let WO : WeierstrassCurve 𝒪 := (Wu ℓ).map ρ
  let DO : LevelPData 𝒪 := (Du ℓ).map ρ
  have hDO : IsLevelPStructure WO ℓ DO := (isLevelPStructure_Wu ℓ).map ρ
  have hℓO : IsUnit ((ℓ : ℕ) : (𝒪 : Type u)) := by simpa using (isUnit_natCast_Ru ℓ).map ρ

  have hDK : IsLevelPStructure (WO.map (algebraMap 𝒪 K)) ℓ (DO.map (algebraMap 𝒪 K)) := hDO.map _
  have hDΩ : IsLevelPStructure (WO.map ψ) ℓ (DO.map ψ) := hDO.map _
  have hSK := nonsingular_P (WO.map (algebraMap 𝒪 K)) hDK
  have hTK := nonsingular_Q (WO.map (algebraMap 𝒪 K)) hDK
  have hSΩ := nonsingular_P (WO.map ψ) hDΩ
  have hTΩ := nonsingular_Q (WO.map ψ) hDΩ
  have hSKn := zsmul_some_eq_zero (WO.map (algebraMap 𝒪 K)) hℓ2 hSK hDK.preΨ_P
  have hTKn := zsmul_some_eq_zero (WO.map (algebraMap 𝒪 K)) hℓ2 hTK hDK.preΨ_Q
  have hSΩn := zsmul_some_eq_zero (WO.map ψ) hℓ2 hSΩ hDΩ.preΨ_P
  have hTΩn := zsmul_some_eq_zero (WO.map ψ) hℓ2 hTΩ hDΩ.preΨ_Q
  obtain ⟨u, hu1, hu2⟩ :=
    WeierstrassCurve.Affine.exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring 𝒪 ψ WO ℓ hℓO
      DO.xP DO.yP DO.xQ DO.yQ hSK hTK hSΩ hTΩ hSKn hTKn hSΩn hTΩn
  refine ⟨u, ?_, ?_⟩
  · rw [hu1]
    exact (V_congr _ _ _ _ (WeierstrassCurve.map_map (Wu ℓ) ρ (algebraMap 𝒪 K)).symm rfl).trans
      (V_eq_some (WO.map (algebraMap 𝒪 K)) (DO.map (algebraMap 𝒪 K)) hSK hTK)
  · rw [hu2]
    exact (V_congr _ _ _ _ (WeierstrassCurve.map_map (Wu ℓ) ρ ψ).symm rfl).trans
      (V_eq_some (WO.map ψ) (DO.map ψ) hSΩ hTΩ)

theorem exists_universal (hℓ2 : ℓ ≠ 2) :
    ∃ ε : Ru.{u} ℓ, ε ^ ℓ = 1 ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : Ru.{u} ℓ →+* Ω), cU ℓ Ω φ = φ ε :=
  IsNoetherianRing.exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring (Ru ℓ) ℓ (isUnit_natCast_Ru ℓ)
    (cU ℓ) (cU_pow ℓ hℓ2) (cU_val ℓ hℓ2)

end Rule

end P2M.RelWeilZar
p2m_reactivate "P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq.P2M P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq.P2M.RelWeilZar"
p2m_reactivate "P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq.P2M"

open P2M.RelWeilZar in
theorem solution
    (A₀ : Type u) [CommRing A₀] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A₀))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (L₁ L₃ : ModularCurve.LevelComponent.{u} A₀)
    (B : Type u) [CommRing B] [Algebra A₀ B]
    (w : (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).Raw B)
    (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ f : B, f ∉ 𝔭 ∧ ∃ ε : Localization.Away f, ε ^ ℓ = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : Localization.Away f →ₐ[A₀] Ω),
        (letI x := (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.mapRing
            (φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away f))) w;
         letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩;
          ((WeierstrassCurve.Affine.weilPairing0 (x.curve) Ω (ℓ : ℤ)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xP (x.level.2.1).yP)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xQ (x.level.2.1).yQ) : Ωˣ) :
            Ω)) = φ ε := by

  let R : ModularCurve.RigidWeierstrassData.{u} A₀ := (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid
  let Vraw : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω],
      (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).Raw Ω → Ω :=
    fun Ω _ _ _ _ x =>
      letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩
      ((WeierstrassCurve.Affine.weilPairing0 (x.curve) Ω (ℓ : ℤ)
          (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xP (x.level.2.1).yP)
          (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xQ (x.level.2.1).yQ) : Ωˣ) : Ω)

  have hD : IsLevelPStructure w.curve ℓ w.level.2.1 := w.isLevel.2.1
  have hΔ : IsUnit w.curve.Δ := w.isUnit_Δ
  have hℓB : IsUnit ((ℓ : ℕ) : B) := by simpa using hℓA.map (algebraMap A₀ B)
  have hℓ2 : ℓ ≠ 2 := by omega

  obtain ⟨εu, hεu, hεu'⟩ := exists_universal ℓ hℓ2
  let χB : Ru.{u} ℓ →+* B := χ ℓ hD hΔ hℓB
  refine ⟨1, fun h1 => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h1),
    algebraMap B (Localization.Away (1 : B)) (χB εu), ?_, ?_⟩
  · rw [← map_pow, ← map_pow, hεu, map_one, map_one]
  intro Ω _ _ _ _ φ
  let θ' : B →ₐ[A₀] Ω := φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away (1 : B)))
  show Vraw Ω (R.mapRing θ' w) = φ (algebraMap B (Localization.Away (1 : B)) (χB εu))
  have step1 : Vraw Ω (R.mapRing θ' w) =
      V ℓ Ω (w.curve.map θ'.toRingHom) ((R.mapRing θ' w).isUnit_Δ) (w.level.2.1.map θ'.toRingHom) := rfl
  have hW : w.curve.map θ'.toRingHom = (Wu ℓ).map (θ'.toRingHom.comp χB) := by
    rw [← WeierstrassCurve.map_map, map_Wu_χ]
  have hDD : w.level.2.1.map θ'.toRingHom = (Du ℓ).map (θ'.toRingHom.comp χB) := by
    rw [← LevelPData.map_map, map_Du_χ]
  have step2 : V ℓ Ω (w.curve.map θ'.toRingHom) ((R.mapRing θ' w).isUnit_Δ) (w.level.2.1.map θ'.toRingHom) =
      cU ℓ Ω (θ'.toRingHom.comp χB) :=
    V_congr _ _ _ _ hW hDD
  rw [step1, step2, hεu' Ω (θ'.toRingHom.comp χB)]
  rfl

end S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
end P2MW
export P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq (solution)
