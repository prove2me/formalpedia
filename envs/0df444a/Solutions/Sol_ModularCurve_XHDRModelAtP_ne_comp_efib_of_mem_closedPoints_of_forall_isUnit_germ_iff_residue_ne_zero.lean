-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1a2474be-c652-51c2-8be5-768a8cfddf5b

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

universe u

namespace NCfin

theorem aux_comp_app_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) :
    ((f ≫ g).app U).hom s = (f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) := by
  rw [Scheme.Hom.comp_app]; rfl

theorem aux_germ_app_congr3 {X Y Z T : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T) {h : X ⟶ T} (e : a ≫ b ≫ c = h)
    (W : T.Opens) (s : Γ(T, W)) (x : X) (hx₁ : x ∈ a ⁻¹ᵁ (b ⁻¹ᵁ (c ⁻¹ᵁ W))) (hx₂ : x ∈ h ⁻¹ᵁ W) :
    (X.presheaf.germ (a ⁻¹ᵁ (b ⁻¹ᵁ (c ⁻¹ᵁ W))) x hx₁).hom ((a.app (b ⁻¹ᵁ (c ⁻¹ᵁ W))).hom ((b.app (c ⁻¹ᵁ W)).hom ((c.app W).hom s))) =
      (X.presheaf.germ (h ⁻¹ᵁ W) x hx₂).hom ((h.app W).hom s) := by
  subst e
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app]
  rfl

theorem aux_genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty (U : Scheme.{u})] :
    genericPoint X ∈ U := by
  obtain ⟨⟨x, hx⟩⟩ := h
  exact ((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open U.2 hx

end NCfin

namespace NCfin

theorem ev_base {X : Scheme.{u}} {A κ : CommRingCat.{u}} [IsLocalRing κ] (f : X ⟶ Spec A) (Q : Spec κ ⟶ X) (φ : A ⟶ κ)
    (hQ : Q ≫ f = Spec.map φ) (s : Γ(Spec A, ⊤)) :
    Scheme.stalkClosedPointTo Q (X.presheaf.germ ⊤ (Q.base (closedPoint κ)) trivial (f.appTop s)) = φ ((Scheme.ΓSpecIso A).hom s) := by
  have h1 : X.presheaf.germ ⊤ (Q.base (closedPoint κ)) trivial (f.appTop s) =
      f.stalkMap (Q.base (closedPoint κ)) ((Spec A).presheaf.germ ⊤ (f.base (Q.base (closedPoint κ))) trivial s) :=
    (Scheme.Hom.germ_stalkMap_apply f ⊤ (Q.base (closedPoint κ)) trivial s).symm
  rw [h1, ← CategoryTheory.comp_apply, ← Scheme.stalkClosedPointTo_comp]
  have key : ∀ g : Spec κ ⟶ Spec A, g = Spec.map φ →
      Scheme.stalkClosedPointTo g ((Spec A).presheaf.germ ⊤ (g.base (closedPoint κ)) trivial s) = φ ((Scheme.ΓSpecIso A).hom s) := by
    intro g hg
    subst hg
    have := Scheme.germ_stalkClosedPointTo_Spec (R := A) (S := κ) φ
    exact congrArg (fun k => (k : Γ(Spec A, ⊤) ⟶ κ) s) this
  exact key (Q ≫ f) hQ

end NCfin

namespace NCfin

theorem germ_app_res_top {X X' : Scheme.{u}} (h : X' ⟶ X) (U : X.Opens) (z : Γ(X, ⊤)) (x : X') (hx : x ∈ h ⁻¹ᵁ U) :
    (X'.presheaf.germ (h ⁻¹ᵁ U) x hx).hom ((h.app U).hom ((X.presheaf.map (homOfLE le_top).op).hom z)) =
      (X'.presheaf.germ ⊤ x trivial).hom ((h.appTop).hom z) := by
  rw [← Scheme.Hom.germ_stalkMap_apply h U x hx, TopCat.Presheaf.germ_res_apply]
  exact Scheme.Hom.germ_stalkMap_apply h ⊤ x trivial z

theorem germ_appTop_comp_SpecMap {C : Scheme.{u}} [IsIntegral C] {K A : CommRingCat.{u}} (c : C ⟶ Spec K) (φ : A ⟶ K)
    {g : C ⟶ Spec A} (hg : c ≫ Spec.map φ = g) (a : A) :
    (C.presheaf.germ ⊤ (genericPoint C) trivial).hom ((g.appTop).hom ((Scheme.ΓSpecIso A).inv a)) =
      (C.presheaf.germ ⊤ (genericPoint C) trivial).hom ((c.appTop).hom ((Scheme.ΓSpecIso K).inv (φ a))) := by
  subst hg
  congr 1
  rw [show ((c ≫ Spec.map φ).appTop).hom ((Scheme.ΓSpecIso A).inv a) = (c.appTop).hom (((Spec.map φ).appTop).hom ((Scheme.ΓSpecIso A).inv a)) from by
    rw [Scheme.Hom.comp_appTop]; rfl]
  congr 1
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, Scheme.ΓSpecIso_inv_naturality]

end NCfin

namespace NCQ

noncomputable def jNumInv : PowerSeries ℤ := jNum.invOfUnit 1

theorem jNum_mul_jNumInv : jNum * jNumInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum]; rfl)

noncomputable def jqInv (K : Type*) [CommRing K] : LaurentSeries K :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNumInv.map (Int.castRingHom K))

theorem jqModC_mul_jqInv (K : Type*) [CommRing K] : jqModC K * jqInv K = 1 := by
  rw [jqModC, jqInv, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul (HahnSeries.ofPowerSeries ℤ K),
    ← map_mul, jNum_mul_jNumInv, map_one, map_one, mul_one]
  norm_num

theorem map_jqInv {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') : (jqInv K).map f = jqInv K' := by
  have hmul : ∀ x y : LaurentSeries K, (x * y).map f = x.map f * y.map f :=
    fun x y => HahnSeries.map_mul f.toNonUnitalRingHom
  have hsingle : (HahnSeries.single (1 : ℤ) (1 : K)).map f = HahnSeries.single (1 : ℤ) 1 := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f, map_one, map_zero]
  have hseries : ∀ u : PowerSeries K, (HahnSeries.ofPowerSeries ℤ K u).map f = HahnSeries.ofPowerSeries ℤ K' (u.map f) := by
    intro u
    ext k
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  rw [jqInv, jqInv, hmul, hsingle, hseries,
    show (jNumInv.map (Int.castRingHom K)).map f = jNumInv.map (Int.castRingHom K') from by
      rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom K) jNumInv)
            = PowerSeries.map (f.comp (Int.castRingHom K)) jNumInv from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom K) f)) jNumInv).symm,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]]

theorem jqInv_ne_zero (K : Type*) [CommRing K] [Nontrivial K] : jqInv K ≠ 0 := by
  intro h
  have := jqModC_mul_jqInv K
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem coeff_jqModC_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  rw [jqModC, HahnSeries.coeff_single_mul, one_mul, show (-1 : ℤ) - -1 = ((0 : ℕ) : ℤ) by norm_num,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

theorem jqModC_sub_single_ne_zero (K : Type*) [CommRing K] [Nontrivial K] (c : K) :
    jqModC K - HahnSeries.single (0 : ℤ) c ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff (-1)) h
  simp only [HahnSeries.coeff_sub, coeff_jqModC_neg_one, HahnSeries.coeff_single, HahnSeries.coeff_zero] at h1
  norm_num at h1

theorem transport {L : Type*} [Field L] {A' : ValuationSubring L} {F Fbar : Type*} [Field F] [Algebra L F] [Field Fbar] [Algebra (ResidueField A') Fbar]
    (R : RegularProlongation A' F Fbar) {x x' : F} (e : x = x') (P : Fbar → Prop)
    (hx : ∃ h : x ∈ R.integers, P (R.residue ⟨x, h⟩)) : ∃ h : x' ∈ R.integers, P (R.residue ⟨x', h⟩) := by
  subst e; exact hx

section Kit

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
  (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
  (xj : ↥(xHFunctionFieldBar M H)) (hxj : ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

include hxj in

theorem residue_sub_algebraMap (a : ↥A) :
    ∃ h : xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
          jqModC (ResidueField ↥A) - HahnSeries.single (0 : ℤ) (IsLocalRing.residue ↥A a) ∧
        Rpd.R₁.residue ⟨_, h⟩ ≠ 0 := by
  set y : LaurentSeries ↥A := jqModC ↥A - HahnSeries.single (0 : ℤ) a with hy
  have hcoe : coeffMap A.subtype y = ((xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) :
      LaurentSeries (AlgebraicClosure ℚ)) := by
    have hjA : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := map_jqModC A.subtype
    rw [hy, map_sub, hjA, coeffMap_single]
    have hsub : (((xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) - ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) :=
      map_sub (xHFunctionFieldBar M H).val xj _
    rw [hsub, hxj]
    congr 1
    rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) from rfl,
      algebraMap_laurentSeries_eq_single]
    rfl
  have hmem : coeffMap A.subtype y ∈ xHFunctionFieldBar M H := by rw [hcoe]; exact SetLike.coe_mem _
  have heq : (⟨coeffMap A.subtype y, hmem⟩ : ↥(xHFunctionFieldBar M H)) = xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) :=
    Subtype.ext hcoe
  have hres' : coeffMap (IsLocalRing.residue ↥A) y = jqModC (ResidueField ↥A) - HahnSeries.single (0 : ℤ) (IsLocalRing.residue ↥A a) := by
    have hjκ : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := map_jqModC _
    rw [hy, map_sub, hjκ, coeffMap_single]
  have key : ∃ h : (⟨coeffMap A.subtype y, hmem⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
          jqModC (ResidueField ↥A) - HahnSeries.single (0 : ℤ) (IsLocalRing.residue ↥A a) ∧ Rpd.R₁.residue ⟨_, h⟩ ≠ 0 := by
    obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap y hmem
    refine ⟨h, hres.trans hres', fun h0 => ?_⟩
    have := hres.trans hres'
    rw [h0] at this
    exact jqModC_sub_single_ne_zero (ResidueField ↥A) _ (by rw [← this]; rfl)
  exact transport Rpd.R₁ heq (fun r => ((r : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
      jqModC (ResidueField ↥A) - HahnSeries.single (0 : ℤ) (IsLocalRing.residue ↥A a) ∧ r ≠ 0) key

include hxj in
theorem residue_sub_algebraMap_ne_zero (a : ↥A) :
    ∃ h : xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers,
      Rpd.R₁.residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨h, -, hne⟩ := residue_sub_algebraMap p M H hpM A θ Psp Rpd xj hxj a
  exact ⟨h, hne⟩

include hxj in

theorem residue_inv :
    ∃ h : xj⁻¹ ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqInv (ResidueField ↥A) ∧
        Rpd.R₁.residue ⟨_, h⟩ ≠ 0 := by
  have hcoeinv : ((xj⁻¹ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqInv (AlgebraicClosure ℚ) := by
    have h1 : ((xj⁻¹ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ :=
      map_inv₀ (xHFunctionFieldBar M H).val xj
    rw [h1, hxj]
    exact inv_eq_of_mul_eq_one_right (jqModC_mul_jqInv _)
  have hcoe : coeffMap A.subtype (jqInv ↥A) = ((xj⁻¹ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hcoeinv]; exact map_jqInv _
  have hmem : coeffMap A.subtype (jqInv ↥A) ∈ xHFunctionFieldBar M H := by rw [hcoe]; exact SetLike.coe_mem _
  have heq : (⟨coeffMap A.subtype (jqInv ↥A), hmem⟩ : ↥(xHFunctionFieldBar M H)) = xj⁻¹ := Subtype.ext hcoe
  have hres' : coeffMap (IsLocalRing.residue ↥A) (jqInv ↥A) = jqInv (ResidueField ↥A) := map_jqInv _
  have key : ∃ h : (⟨coeffMap A.subtype (jqInv ↥A), hmem⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqInv (ResidueField ↥A) ∧ Rpd.R₁.residue ⟨_, h⟩ ≠ 0 := by
    obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap (jqInv ↥A) hmem
    refine ⟨h, hres.trans hres', fun h0 => ?_⟩
    have := hres.trans hres'
    rw [h0] at this
    exact jqInv_ne_zero (ResidueField ↥A) (by rw [← this]; rfl)
  exact transport Rpd.R₁ heq (fun r => ((r : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqInv (ResidueField ↥A) ∧ r ≠ 0) key

include hxj in
theorem residue_inv_ne_zero :
    ∃ h : xj⁻¹ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨h, -, hne⟩ := residue_inv p M H hpM A θ Psp Rpd xj hxj
  exact ⟨h, hne⟩

end Kit

end NCQ

set_option maxHeartbeats 3200000 in

theorem false_of_mem_finChart
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    ∀ c : ↥(XO (ΓM M H) hj ρ), (XO.toBase (ΓM M H) hj ρ).base c = IsLocalRing.closedPoint ↥A →
      (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
        (g : Γ(XO (ΓM M H) hj ρ, V)) (hc : c ∈ V),
        letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
          (𝔛.Meta).ffEquiv.symm.toRingHom.comp
            (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
              ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
        ∃ h : readA g ∈ Rpd.R₁.integers,
          (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V c hc g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0)) →
      ∀ (i : Fin 2) (w : ↥(𝔛.Mfib A hA ρ hρ).C), w ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C →
        c ∈ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) →
        c ≠ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base w := by

  intro c hcA hdom i w hw hcV heq
  classical

  set fstA := pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) with hfstA
  set prA : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) with hprA
  haveI := 𝔛.Meta_chart_nonempty
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral

  set q := pointOfClosedPoint (𝔛.Mfib A hA ρ hρ).toBase w hw with hq
  set Q := q ≫ 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl with hQdef
  have hQc : Q.base (closedPoint (ResidueField ↥A)) = c := by
    rw [heq, hQdef, Scheme.Hom.comp_apply, hq, pointOfClosedPoint_apply]
  have hQbase : Q ≫ XO.toBase (ΓM M H) hj ρ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
    rw [hQdef]
    change q ≫ 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl ≫ pullback.snd _ _ = _
    rw [bcMap_snd, ← Category.assoc (𝔛.comp A hA ρ hρ i), 𝔛.comp_over, ← Category.assoc (𝔛.efib A hA ρ hρ), 𝔛.hefib,
      ← Category.assoc, hq, pointOfClosedPoint_comp, Category.id_comp]

  subst hQc

  have hprA_fst : prA ≫ fstA = pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
    rw [hprA, hfstA, pullback.lift_fst, Category.comp_id]
  have heA : 𝔛.eeta ≫ prA ≫ fstA = 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
    rw [hprA_fst]
  have hgenQ : genericPoint (𝔛.Meta).C ∈ (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) :=
    NCfin.aux_genericPoint_mem_of_nonempty _
  have hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (fstA ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))) := by
    have h := hgenQ
    rw [← heA, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage] at h
    exact h
  set V : (XO (ΓM M H) hj ρ).Opens := fstA ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) with hV

  set jel : ↥(chartAlgFin p (ΓM M H) hj) := AlgebraicCurve.TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) with hjel
  set t : Γ(XO (ΓM M H) hj ρ, V) :=
      (fstA.app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
        (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv jel)) with ht
  set readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (V))) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (V))).hom.comp (prA.app (V)).hom)) with hreadA
  have hxj : ((readA t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hreadA, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ht,
      NCfin.aux_germ_app_congr3 𝔛.eeta prA fstA heA ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) _ (genericPoint (𝔛.Meta).C) hgenV hgenQ]
    refine (𝔛.Meta_pin jel).trans ?_
    rw [hjel, AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin, XHDRLevel.coe_jAt]
    exact coeffMap_jqModC _

  let cst : ↥A → Γ(XO (ΓM M H) hj ρ, V) := fun o =>
    (XO (ΓM M H) hj ρ).presheaf.map (homOfLE le_top).op ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv o))
  have hev_cst : ∀ o : ↥A, Scheme.stalkClosedPointTo Q ((XO (ΓM M H) hj ρ).presheaf.germ V _ hcV (cst o)) = IsLocalRing.residue ↥A o := by
    intro o
    have hg : (XO (ΓM M H) hj ρ).presheaf.germ V _ hcV (cst o) =
        (XO (ΓM M H) hj ρ).presheaf.germ ⊤ (Q.base (closedPoint (ResidueField ↥A))) trivial
          ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv o)) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hg, NCfin.ev_base (XO.toBase (ΓM M H) hj ρ) Q (CommRingCat.ofHom (IsLocalRing.residue ↥A)) hQbase]
    show IsLocalRing.residue ↥A ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv o)) = _
    rw [← CategoryTheory.comp_apply, Iso.inv_hom_id]
    rfl

  obtain ⟨a0, ha0⟩ := IsLocalRing.residue_surjective (Scheme.stalkClosedPointTo Q ((XO (ΓM M H) hj ρ).presheaf.germ V _ hcV t))

  have hnot : ¬ IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ hcV (t - cst a0)) := by
    intro hu
    have hu' := hu.map (Scheme.stalkClosedPointTo Q).hom
    rw [map_sub, map_sub, hev_cst a0, ha0, sub_self] at hu'
    exact not_isUnit_zero hu'

  obtain ⟨h, hiff⟩ := hdom V hgenV (t - cst a0) hcV
  have hread_cst : readA (cst a0) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a0 : AlgebraicClosure ℚ) := by

    have hprA_snd : prA ≫ XO.toBase (ΓM M H) hj ρ =
        pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ≫ Spec.map (CommRingCat.ofHom A.subtype) := by
      rw [hprA]; exact pullback.lift_snd _ _ _
    have hbase : 𝔛.Meta.toBase ≫ Spec.map (CommRingCat.ofHom A.subtype) = (𝔛.eeta ≫ prA) ≫ XO.toBase (ΓM M H) hj ρ := by
      rw [Category.assoc, hprA_snd, ← Category.assoc, 𝔛.heeta]
    have step1 : ((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom
          ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom ((prA.app V).hom (cst a0))) =
        ((𝔛.Meta).C.presheaf.germ ⊤ (genericPoint (𝔛.Meta).C) trivial).hom
          ((((𝔛.eeta ≫ prA) ≫ XO.toBase (ΓM M H) hj ρ).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a0)) := by
      have e1 : (𝔛.eeta.app (prA ⁻¹ᵁ V)).hom ((prA.app V).hom (cst a0)) = ((𝔛.eeta ≫ prA).app V).hom (cst a0) := by
        rw [NCfin.aux_comp_app_apply]
      rw [e1]
      rw [show (𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV =
          (𝔛.Meta).C.presheaf.germ ((𝔛.eeta ≫ prA) ⁻¹ᵁ V) (genericPoint (𝔛.Meta).C) hgenV from rfl]
      have hcst : cst a0 = (XO (ΓM M H) hj ρ).presheaf.map (homOfLE le_top).op ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a0)) := rfl
      rw [hcst]
      erw [NCfin.germ_app_res_top (𝔛.eeta ≫ prA) V ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a0)) (genericPoint (𝔛.Meta).C) hgenV]
      try (congr 1; rw [Scheme.Hom.comp_appTop]; done)
      try rfl
    have step2 := NCfin.germ_appTop_comp_SpecMap (𝔛.Meta).toBase (CommRingCat.ofHom A.subtype) hbase a0
    show (𝔛.Meta).ffEquiv.symm (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom
          ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom ((prA.app V).hom (cst a0)))) = _
    rw [step1, step2, RingEquiv.symm_apply_eq, (𝔛.Meta).ffEquiv_algebraMap]
    rfl
  have hne : Rpd.R₁.residue ⟨_, h⟩ ≠ 0 := by
    obtain ⟨h', hne'⟩ := NCQ.residue_sub_algebraMap_ne_zero p M H hpM A θ Psp Rpd (readA t) hxj a0
    have helt : readA (t - cst a0) = readA t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a0 : AlgebraicClosure ℚ) := by
      rw [map_sub, hread_cst]
    have : (⟨_, h⟩ : ↥Rpd.R₁.integers) = ⟨_, h'⟩ := Subtype.ext helt
    rw [this]
    exact hne'
  exact hnot (hiff.mpr hne)

section PoleHalf

namespace NCPole

theorem stalkMap_germ_appIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : ↥X) (s : Γ(X, ⊤))
    (hx : f.base x ∈ f ''ᵁ ⊤) :
    f.stalkMap x (Y.presheaf.germ (f ''ᵁ ⊤) (f.base x) hx ((f.appIso ⊤).inv s)) = X.presheaf.germ ⊤ x trivial s := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have := congrArg (fun φ => φ.hom s) (Scheme.Hom.appIso_inv_app f ⊤)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this]
  exact TopCat.Presheaf.germ_res_apply' _ _ _ _ _

theorem stalkMap_germ_top {X Y : Scheme.{u}} (f : X ⟶ Y) (x : ↥X) (y : Γ(Y, ⊤)) :
    f.stalkMap x (Y.presheaf.germ ⊤ (f.base x) trivial y) = X.presheaf.germ ⊤ x trivial (f.appTop y) :=
  Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial y

theorem ΓSpecIso_inv_appTop {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop).hom r = (φ ≫ (Scheme.ΓSpecIso S).inv).hom r
  rw [Scheme.ΓSpecIso_inv_naturality]

theorem comp_app_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (t : Γ(Z, U)) :
    ((f ≫ g).app U).hom t = (f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom t) := rfl

theorem app_appIso_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (s : Γ(X, ⊤)) :
    (f.app (f ''ᵁ ⊤)).hom ((f.appIso ⊤).inv s) = (X.presheaf.map (eqToHom (f.preimage_image_eq ⊤)).op).hom s := by
  have := congrArg (fun φ => φ.hom s) (Scheme.Hom.appIso_inv_app f ⊤)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem germ_map_eqToHom_apply {X : Scheme.{u}} {U V : X.Opens} (e : U = V) (x : ↥X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.presheaf.germ V x hx ((X.presheaf.map (eqToHom e.symm).op).hom s) = X.presheaf.germ U x (e ▸ hx) s := by
  subst e
  simp

theorem isUnit_germ_appIso_inv_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : ↥X) (s : Γ(X, ⊤))
    (hx : f.base x ∈ f ''ᵁ ⊤) :
    IsUnit (Y.presheaf.germ (f ''ᵁ ⊤) (f.base x) hx ((f.appIso ⊤).inv s)) ↔ IsUnit (X.presheaf.germ ⊤ x trivial s) := by
  rw [← isUnit_map_iff (f.stalkMap x).hom, stalkMap_germ_appIso_inv]

section TwoChart
open AlgebraicCurve.TwoChartIntegralModel
variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem mem_range_of_jInv_not_mem (y : XInf R F j) (h : jInvChartInf R F j ∉ y.asIdeal) :
    (TwoChartIntegralModel.ιInf R F j).base y ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  have hy : y ∈ (PrimeSpectrum.basicOpen (jInvChartInf R F j) : Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j))) := h
  rw [← PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)] at hy
  obtain ⟨x, hx⟩ := hy
  have hx' : (fInf R F j).base x = y := hx
  refine ⟨(fFin R F j).base x, ?_⟩
  rw [← hx', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition]

theorem mem_range_ιInf_of_j_not_mem (z : XFin R F j) (h : jChartFin R F j ∉ z.asIdeal) :
    (TwoChartIntegralModel.ιFin R F j).base z ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  have hz : z ∈ (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin R F j))) := h
  rw [← PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)] at hz
  obtain ⟨x, hx⟩ := hz
  have hx' : (fFin R F j).base x = z := hx
  refine ⟨(fInf R F j).base x, ?_⟩
  rw [← hx', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition]

theorem exists_fFin_eq_of_j_not_mem (z : XFin R F j) (h : jChartFin R F j ∉ z.asIdeal) :
    ∃ m : ↥(XMid R F j), (fFin R F j).base m = z := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  have hz : z ∈ (PrimeSpectrum.basicOpen (jChartFin R F j) : Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin R F j))) := h
  rw [← PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)] at hz
  exact hz

set_option maxHeartbeats 1600000 in

theorem germ_jInv_mul_germ_j_eq_one (m : ↥(XMid R F j)) (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : x = (fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base m)
    (h1 : x ∈ (TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤) (h2 : x ∈ (TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤) :
    (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ x h1 (((TwoChartIntegralModel.ιInf R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv (jInvChartInf R F j))) * (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ x h2 (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv (jChartFin R F j))) = 1 := by
  subst hx
  apply ((asIso ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).stalkMap m)).commRingCatIsoToRingEquiv).injective
  rw [map_mul, map_one]
  have hB1 : (asIso ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).stalkMap m)).commRingCatIsoToRingEquiv ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base m) h1 (((TwoChartIntegralModel.ιInf R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv (jInvChartInf R F j)))) =
      (XMid R F j).presheaf.germ ⊤ m trivial
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid R F j))).inv (inclInf R F j (jInvChartInf R F j))) := by
    show ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).stalkMap m) _ = _
    rw [Scheme.Hom.stalkMap_comp]
    show (fInf R F j).stalkMap m ((TwoChartIntegralModel.ιInf R F j).stalkMap ((fInf R F j).base m)
      ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ ((TwoChartIntegralModel.ιInf R F j).base ((fInf R F j).base m)) h1 (((TwoChartIntegralModel.ιInf R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv (jInvChartInf R F j))))) = _
    rw [stalkMap_germ_appIso_inv (TwoChartIntegralModel.ιInf R F j) ((fInf R F j).base m)]
    rw [stalkMap_germ_top, ΓSpecIso_inv_appTop]
    rfl
  have hB2 : (asIso ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).stalkMap m)).commRingCatIsoToRingEquiv ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base m) h2 (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv (jChartFin R F j)))) =
      (XMid R F j).presheaf.germ ⊤ m trivial
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid R F j))).inv (inclFin R F j (jChartFin R F j))) := by
    show ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).stalkMap m) _ = _
    have e : (fFin R F j ≫ TwoChartIntegralModel.ιFin R F j).base m = (fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base m := by rw [glue_condition]
    have h2' : (fFin R F j ≫ TwoChartIntegralModel.ιFin R F j).base m ∈ (TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤ := ⟨(fFin R F j).base m, trivial, rfl⟩
    have hg : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ ((fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base m) h2 (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv (jChartFin R F j))) =
        ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalkCongr (.of_eq e)).hom ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ ((fFin R F j ≫ TwoChartIntegralModel.ιFin R F j).base m) h2' (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv (jChartFin R F j)))) := by
      symm
      exact congrArg (fun φ => φ.hom (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv (jChartFin R F j)))) (TopCat.Presheaf.germ_stalkSpecializes (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf h2' (Inseparable.of_eq e).ge)
    rw [hg]
    show (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalkCongr (.of_eq e)).hom ≫ (fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).stalkMap m) _ = _
    rw [← Scheme.Hom.stalkMap_congr_hom _ _ (glue_condition R F j) m, Scheme.Hom.stalkMap_comp]
    show (fFin R F j).stalkMap m ((TwoChartIntegralModel.ιFin R F j).stalkMap ((fFin R F j).base m)
      ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ _ ((TwoChartIntegralModel.ιFin R F j).base ((fFin R F j).base m)) h2' (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv (jChartFin R F j))))) = _
    rw [stalkMap_germ_appIso_inv (TwoChartIntegralModel.ιFin R F j) ((fFin R F j).base m)]
    rw [stalkMap_germ_top, ΓSpecIso_inv_appTop]
    rfl
  rw [hB1, hB2, ← map_mul, ← map_mul]
  have h1j1 : inclInf R F j (jInvChartInf R F j) * inclFin R F j (jChartFin R F j) = 1 := by
    apply Subtype.ext
    show j⁻¹ * j = 1
    exact inv_mul_cancel₀ (Fact.out : j ≠ 0)
  rw [h1j1, map_one, map_one]

end TwoChart

theorem genericPoint_mem {Y : Scheme.{0}} [IsIntegral Y] (U : Y.Opens) (h : Nonempty ↥U) : genericPoint Y ∈ U := by
  obtain ⟨⟨u, hu⟩⟩ := h
  exact (genericPoint_specializes u).mem_open U.2 hu

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem pole_half
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (c : ↥(XO (ΓM M H) hj ρ))
    (HDOM : letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
      letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
        pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
      ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
        (g : Γ(XO (ΓM M H) hj ρ, V)) (hc : c ∈ V),
        letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
          (𝔛.Meta).ffEquiv.symm.toRingHom.comp
            (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
              ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
        ∃ h : readA g ∈ Rpd.R₁.integers,
          (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V c hc g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0))
    (hinf : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base c ∈ Set.range (ιInf p (ΓM M H) hj).base)
    (hfin : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base c ∉ Set.range (ιFin p (ΓM M H) hj).base) :
    False := by

  let XA : Scheme.{0} := XO (ΓM M H) hj ρ
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XA :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let fstA := pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))

  obtain ⟨yc, hyc⟩ := hinf
  have h1j : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ∈ yc.asIdeal := by
    by_contra h
    exact hfin (hyc ▸ mem_range_of_jInv_not_mem (jAt (ΓM M H) hj) yc h)

  let Vinf : XA.Opens := fstA ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)
  have hc' : fstA.base c ∈ (ιInf p (ΓM M H) hj) ''ᵁ ⊤ := ⟨yc, trivial, hyc⟩
  have hc : c ∈ Vinf := hc'
  let sinf := (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv
    (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
  let tinf : Γ(X p (ΓM M H) hj, (ιInf p (ΓM M H) hj) ''ᵁ ⊤) := ((ιInf p (ΓM M H) hj).appIso ⊤).inv sinf
  let ginf : Γ(XA, Vinf) := (fstA.app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom tinf

  let fstQ := pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  have hprfst : prA ≫ fstA = fstQ := by
    simp only [prA, fstA, fstQ, pullback.map, pullback.lift_fst, Category.comp_id]
  let ξ' : ↥XA := (𝔛.eeta ≫ prA).base (genericPoint (𝔛.Meta).C)
  let x₀ : ↥(X p (ΓM M H) hj) := (𝔛.eeta ≫ fstQ).base (genericPoint (𝔛.Meta).C)
  have hx₀ : fstA.base ξ' = x₀ := by
    show ((𝔛.eeta ≫ prA) ≫ fstA).base _ = _
    rw [Category.assoc, hprfst]

  have hgenfinQ : genericPoint (𝔛.Meta).C ∈ (𝔛.eeta ≫ fstQ) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) :=
    genericPoint_mem _ (𝔛.Meta_chart_nonempty)
  have hx₀fin : x₀ ∈ (ιFin p (ΓM M H) hj) ''ᵁ ⊤ := hgenfinQ
  obtain ⟨z₀, -, hz₀⟩ := id hx₀fin

  let sj := (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (jChartFin p (ΓM M H) hj)
  let tj : Γ(X p (ΓM M H) hj, (ιFin p (ΓM M H) hj) ''ᵁ ⊤) := ((ιFin p (ΓM M H) hj).appIso ⊤).inv sj
  have hpin := 𝔛.Meta_pin (jChartFin p (ΓM M H) hj)

  have hkey : (jChartFin p (ΓM M H) hj : ↥(chartAlgFin p (ΓM M H) hj)) ∉ z₀.asIdeal := by
    intro hjz

    have hnu0 : ¬ IsUnit ((X p (ΓM M H) hj).presheaf.germ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) x₀ hx₀fin tj) := by
      have e : x₀ = (ιFin p (ΓM M H) hj).base z₀ := hz₀.symm
      clear_value x₀
      subst e
      rw [isUnit_germ_appIso_inv_iff, ← Scheme.mem_basicOpen, basicOpen_eq_of_affine]
      exact fun h => h hjz

    have hgerm0 : (𝔛.Meta).C.presheaf.germ ((𝔛.eeta ≫ fstQ) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) (genericPoint (𝔛.Meta).C) hgenfinQ
        (((𝔛.eeta ≫ fstQ).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom tj) = 0 := by
      rw [← Scheme.Hom.germ_stalkMap_apply (𝔛.eeta ≫ fstQ) ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) (genericPoint (𝔛.Meta).C) hgenfinQ]
      have hnu1 := hnu0
      rw [← isUnit_map_iff ((𝔛.eeta ≫ fstQ).stalkMap (genericPoint (𝔛.Meta).C)).hom] at hnu1
      simp [isUnit_iff_ne_zero] at hnu1
      exact hnu1

    have h2 := hpin
    erw [show (𝔛.Meta).C.germToFunctionField ((𝔛.eeta ≫ fstQ) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
        (((𝔛.eeta ≫ fstQ).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom tj) = 0 from hgerm0] at h2
    rw [map_zero] at h2
    have h3 := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff (-1)) h2
    have h4 : ((((jChartFin p (ΓM M H) hj : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) = jqModC ℚ := rfl
    rw [h4] at h3
    simp [coeffEmb_coeff, coeff_jqModC_neg_one] at h3

  obtain ⟨m₀, hm₀⟩ := exists_fFin_eq_of_j_not_mem (jAt (ΓM M H) hj) z₀ hkey
  let φ := AlgebraicCurve.TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιInf p (ΓM M H) hj
  have hφ : AlgebraicCurve.TwoChartIntegralModel.fFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ≫ ιFin p (ΓM M H) hj = φ :=
    AlgebraicCurve.TwoChartIntegralModel.glue_condition _ _ _
  have hx₀φ : φ.base m₀ = x₀ := by
    rw [← hφ]
    show (ιFin p (ΓM M H) hj).base ((AlgebraicCurve.TwoChartIntegralModel.fFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).base m₀) = x₀
    rw [hm₀]; exact hz₀
  have hx₀inf : x₀ ∈ (ιInf p (ΓM M H) hj) ''ᵁ ⊤ :=
    ⟨(AlgebraicCurve.TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).base m₀, trivial, hx₀φ⟩

  have hmemV : ∀ U : (X p (ΓM M H) hj).Opens, x₀ ∈ U → genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (fstA ⁻¹ᵁ U)) := by
    intro U hU
    show fstA.base ((𝔛.eeta ≫ prA).base _) ∈ U
    rw [hx₀]; exact hU

  have hgenVinf : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ Vinf) := hmemV _ hx₀inf

  obtain ⟨h, hiff⟩ := HDOM Vinf hgenVinf ginf hc

  have hnu : ¬ IsUnit (XA.presheaf.germ Vinf c hc ginf) := by
    rw [← Scheme.mem_basicOpen]
    have e1 : XA.basicOpen ginf = fstA ⁻¹ᵁ ((X p (ΓM M H) hj).basicOpen tinf) := (Scheme.preimage_basicOpen fstA tinf).symm
    have e2 : (X p (ΓM M H) hj).basicOpen tinf =
        (ιInf p (ΓM M H) hj) ''ᵁ ((Spec (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).basicOpen sinf) :=
      (Scheme.image_basicOpen (ιInf p (ΓM M H) hj) sinf).symm
    have e3 : (Spec (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).basicOpen sinf =
        PrimeSpectrum.basicOpen (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) :=
      basicOpen_eq_of_affine _
    rw [e1]
    intro hmem
    have hmem' : fstA.base c ∈ (X p (ΓM M H) hj).basicOpen tinf := hmem
    rw [e2, ← hyc] at hmem'
    obtain ⟨y', hy', hyy⟩ := hmem'
    have : y' = yc := (ιInf p (ΓM M H) hj).isOpenEmbedding.injective hyy
    subst this
    rw [e3] at hy'
    exact hy' h1j

  have hres0 : Rpd.R₁.residue ⟨_, h⟩ = 0 := by
    by_contra hne
    exact hnu (hiff.mpr hne)

  have hprod : ∀ (x : ↥(X p (ΓM M H) hj)) (hx : x = φ.base m₀)
      (h1 : x ∈ (ιInf p (ΓM M H) hj) ''ᵁ ⊤) (h2 : x ∈ (ιFin p (ΓM M H) hj) ''ᵁ ⊤),
      (X p (ΓM M H) hj).presheaf.germ _ x h1 tinf * (X p (ΓM M H) hj).presheaf.germ _ x h2 tj = 1 :=
    fun x hx h1 h2 => germ_jInv_mul_germ_j_eq_one (jAt (ΓM M H) hj) m₀ x hx h1 h2

  let Vfin : XA.Opens := fstA ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
  let gj : Γ(XA, Vfin) := (fstA.app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom tj
  have hgenVfin : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ Vfin) := hmemV _ hx₀fin
  let readinf : Γ(XA, Vinf) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ Vinf)) (genericPoint (𝔛.Meta).C) hgenVinf).hom.comp
        ((𝔛.eeta.app (prA ⁻¹ᵁ Vinf)).hom.comp (prA.app Vinf).hom))
  let readfin : Γ(XA, Vfin) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ Vfin)) (genericPoint (𝔛.Meta).C) hgenVfin).hom.comp
        ((𝔛.eeta.app (prA ⁻¹ᵁ Vfin)).hom.comp (prA.app Vfin).hom))

  have eread : ∀ (U : XA.Opens) (hU : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U)) (s : Γ(XA, U)),
      (𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U)) (genericPoint (𝔛.Meta).C) hU
          ((𝔛.eeta.app (prA ⁻¹ᵁ U)).hom ((prA.app U).hom s))
        = (𝔛.eeta ≫ prA).stalkMap (genericPoint (𝔛.Meta).C) (XA.presheaf.germ U ξ' hU s) := by
    intro U hU s
    rw [Scheme.Hom.germ_stalkMap_apply]
    rfl

  have hmor : 𝔛.eeta ≫ prA ≫ fstA = 𝔛.eeta ≫ fstQ := by rw [hprfst]
  have hgermeq : (𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ Vfin)) (genericPoint (𝔛.Meta).C) hgenVfin
        ((𝔛.eeta.app (prA ⁻¹ᵁ Vfin)).hom ((prA.app Vfin).hom gj)) =
      (𝔛.Meta).C.germToFunctionField ((𝔛.eeta ≫ fstQ) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
        (((𝔛.eeta ≫ fstQ).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom tj) := by
    have ec := congrArg (fun ψ => ψ.hom tj) (Scheme.Hom.congr_app hmor ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at ec
    show (𝔛.Meta).C.presheaf.germ _ _ hgenVfin (((𝔛.eeta ≫ prA ≫ fstA).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom tj) = _
    rw [ec]
    erw [TopCat.Presheaf.germ_res_apply]
  have hC1 : (((readfin gj : ↥(xHFunctionFieldBar M H))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (jqModC ↥A) := by
    have h4 : ((((jChartFin p (ΓM M H) hj : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) = jqModC ℚ := rfl
    rw [coeffMap_jqModC, ← coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ)), ← h4]
    refine Eq.trans ?_ hpin
    show (((𝔛.Meta).ffEquiv.symm ((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ Vfin)) (genericPoint (𝔛.Meta).C) hgenVfin
        ((𝔛.eeta.app (prA ⁻¹ᵁ Vfin)).hom ((prA.app Vfin).hom gj))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [hgermeq]
  have hjmem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by rw [← hC1]; exact (readfin gj).2
  obtain ⟨hJ, hJres⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hjmem
  have hJeq : (readfin gj : ↥(xHFunctionFieldBar M H)) = ⟨coeffMap A.subtype (jqModC ↥A), hjmem⟩ := Subtype.ext hC1

  have hone : readinf ginf * readfin gj = 1 := by
    simp only [readinf, readfin, RingHom.coe_comp, Function.comp_apply]
    rw [← map_mul, eread Vinf hgenVinf, eread Vfin hgenVfin, ← map_mul]
    have hg1 : XA.presheaf.germ Vinf ξ' hgenVinf ginf * XA.presheaf.germ Vfin ξ' hgenVfin gj = 1 := by
      show XA.presheaf.germ Vinf ξ' hgenVinf ((fstA.app _).hom tinf) * XA.presheaf.germ Vfin ξ' hgenVfin ((fstA.app _).hom tj) = 1
      rw [← Scheme.Hom.germ_stalkMap_apply fstA _ ξ' hgenVinf, ← Scheme.Hom.germ_stalkMap_apply fstA _ ξ' hgenVfin, ← map_mul,
        hprod (fstA.base ξ') (hx₀.trans hx₀φ.symm), map_one]
    rw [hg1, map_one, map_one]
  have hone' : (⟨readinf ginf, h⟩ : ↥Rpd.R₁.integers) * ⟨⟨coeffMap A.subtype (jqModC ↥A), hjmem⟩, hJ⟩ = 1 := by
    apply Subtype.ext
    show readinf ginf * ((⟨coeffMap A.subtype (jqModC ↥A), hjmem⟩ : ↥(xHFunctionFieldBar M H))) = 1
    rw [← hJeq]; exact hone
  have := congrArg Rpd.R₁.residue hone'
  rw [map_mul, map_one, hres0, zero_mul] at this
  exact zero_ne_one this

end NCPole

end PoleHalf

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    ∀ c : ↥(XO (ΓM M H) hj ρ), (XO.toBase (ΓM M H) hj ρ).base c = IsLocalRing.closedPoint ↥A →
      (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
        (g : Γ(XO (ΓM M H) hj ρ, V)) (hc : c ∈ V),
        letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
          (𝔛.Meta).ffEquiv.symm.toRingHom.comp
            (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
              ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
        ∃ h : readA g ∈ Rpd.R₁.integers,
          (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V c hc g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0)) →
      ∀ (i : Fin 2) (w : ↥(𝔛.Mfib A hA ρ hρ).C), w ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C →
        c ≠ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base w  := by
  intro c hc hdom i w hw
  by_cases hcV : c ∈ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
  · exact false_of_mem_finChart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd c hc hdom i w hw hcV
  · intro heq
    have hfin : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base c ∉ Set.range (ιFin p (ΓM M H) hj).base :=
      fun ⟨y, hy⟩ => hcV ⟨y, trivial, hy⟩
    have hinf : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base c ∈ Set.range (ιInf p (ΓM M H) hj).base := by
      rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
          ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base c) with h | h
      · exact absurd h hfin
      · exact h
    exact (NCPole.pole_half p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd c hdom hinf hfin).elim

end S_ModularCurve_XHDRModelAtP_ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero (solution)
