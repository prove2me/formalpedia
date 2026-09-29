-- Prove2me | solution 1 for ModularCurve.exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3e05756e-9bc0-515f-ba38-ce55668ad615

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

import Theorems.Thm_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace QDp

open PDivisibleGroup

section Engine

variable {Rh : Type} [CommRing Rh] [IsDomain Rh] [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
  {p : ℕ} [Fact p.Prime] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  {J : Type} [AddCommGroup J] (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ J)

theorem comp_eq_id (hΔ : Function.Injective Δ) (A B : J → J) (hBA : ∀ y, B (A y) = y) (v : ℕ)
    (φ ψ : 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hφ : ∀ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (Point.ofAlgHom
        ((Point.toAlgHom x).comp (φ : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
        A (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (hψ : ∀ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (Point.ofAlgHom
        ((Point.toAlgHom x).comp (ψ : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
        B (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) :
    φ.comp ψ = BialgHom.id Rh (𝒢.level v) := by
  refine BialgHom.ext fun a => ?_
  refine PDivisibleGroup.eq_of_forall_point_toAlgHom_apply_eq p
    (FaithfulSMul.algebraMap_injective Rh (AlgebraicClosure ℚ)) 𝒢 v _ _ fun x => ?_

  set y : 𝒢.Point (AlgebraicClosure ℚ) v :=
    Point.ofAlgHom ((Point.toAlgHom x).comp (φ : 𝒢.level v →ₐ[Rh] 𝒢.level v)) with hy
  set z : 𝒢.Point (AlgebraicClosure ℚ) v :=
    Point.ofAlgHom ((Point.toAlgHom y).comp (ψ : 𝒢.level v →ₐ[Rh] 𝒢.level v)) with hz
  have h1 : Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul z)) =
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) := by
    rw [hz, hψ y, hy, hφ x, hBA]
  have h2 : z = x := by
    have h3 := 𝒢.pointsMkAdd_injective (L := AlgebraicClosure ℚ) v (hΔ h1)
    exact Additive.ofMul.injective h3
  have h4 : Point.toAlgHom z = Point.toAlgHom x := by rw [h2]
  have h5 := AlgHom.congr_fun h4 a
  exact h5

end Engine

section Diamond

variable {Rh : Type} [CommRing Rh] [IsDomain Rh] [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
  {p : ℕ} [Fact p.Prime] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)

omit [IsDomain Rh] [FaithfulSMul Rh (AlgebraicClosure ℚ)] [Fact p.Prime] in
theorem genOpH_dia_dia_inv (d : (ZMod M)ˣ) (y : ModularCurve.JH M H) :
    ModularCurve.genOpH M H S (CohCarrier.Gen.dia d) (ModularCurve.genOpH M H S (CohCarrier.Gen.dia d⁻¹) y) = y := by
  rw [ModularCurve.genOpH_dia, ModularCurve.genOpH_dia, ← ModularCurve.diamondHBar_mul, mul_inv_cancel,
    ModularCurve.diamondHBar_apply_eq_self_of_mem M H 1 (one_mem H)]

omit [IsDomain Rh] [FaithfulSMul Rh (AlgebraicClosure ℚ)] [Fact p.Prime] in
theorem genOpH_dia_inv_dia (d : (ZMod M)ˣ) (y : ModularCurve.JH M H) :
    ModularCurve.genOpH M H S (CohCarrier.Gen.dia d⁻¹) (ModularCurve.genOpH M H S (CohCarrier.Gen.dia d) y) = y := by
  rw [ModularCurve.genOpH_dia, ModularCurve.genOpH_dia, ← ModularCurve.diamondHBar_mul, inv_mul_cancel,
    ModularCurve.diamondHBar_apply_eq_self_of_mem M H 1 (one_mem H)]

theorem exists_bialgEquiv_coe_eq (hΔ : Function.Injective Δ) (d : (ZMod M)ˣ)
    (φ ψ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hφ : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (Point.ofAlgHom
        ((Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
        ModularCurve.genOpH M H S (CohCarrier.Gen.dia d) (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (hψ : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (Point.ofAlgHom
        ((Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
        ModularCurve.genOpH M H S (CohCarrier.Gen.dia d⁻¹) (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) :
    ∃ Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) = φ v) ∧
      (∀ v : ℕ, ((Dp v).symm : 𝒢.level v →ₐc[Rh] 𝒢.level v) = ψ v) := by
  have h₁ : ∀ v, (φ v).comp (ψ v) = BialgHom.id Rh (𝒢.level v) := fun v =>
    comp_eq_id 𝒢 Δ hΔ _ _ (genOpH_dia_inv_dia M H S d) v (φ v) (ψ v) (hφ v) (hψ v)
  have h₂ : ∀ v, (ψ v).comp (φ v) = BialgHom.id Rh (𝒢.level v) := fun v =>
    comp_eq_id 𝒢 Δ hΔ _ _ (genOpH_dia_dia_inv M H S d) v (ψ v) (φ v) (hψ v) (hφ v)
  refine ⟨fun v => BialgEquiv.ofBialgHom (φ v) (ψ v) (h₁ v) (h₂ v), fun v => ?_, fun v => ?_⟩
  · exact BialgEquiv.coe_ofBialgHom _ _ _ _
  · rw [BialgEquiv.ofBialgHom_symm]
    exact BialgEquiv.coe_ofBialgHom _ _ _ _

end Diamond

end QDp

set_option linter.unusedVariables false in
open ModularCurve in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    (S : Set ℕ) (d : (ZMod M)ˣ)

    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (heinj : Function.Injective e)
    (herange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))
    (hegal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x))
    (hsat : ∀ y : TateModule p (ModularCurve.JH M H), (p : ℤ_[p]) • y ∈ LinearMap.range e → y ∈ LinearMap.range e)
    (hcoker : Nonempty ((TateModule p (ModularCurve.JH M H) ⧸ LinearMap.range e) ≃ₗ[ℤ_[p]] (Fin O.toricRank → ℤ_[p])))
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    {hB : ℕ}
    (ℬ : PDivisibleGroup Rh p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    {h' : ℕ}
    (hhB : h = O.toricRank + hB)
    (hhB2 : hB = 2 * h')
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    (hψred : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hperiod : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)
    :
    ∃ Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] 𝒢.level (v + 1)) =
        (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
        ι v ≫ (O.hecke S (CohCarrier.Gen.dia d)).1) := by
  obtain ⟨φ, hφt, hφι, hφpts⟩ := hιhecke S (CohCarrier.Gen.dia d)
  obtain ⟨ψ, -, -, hψpts⟩ := hιhecke S (CohCarrier.Gen.dia d⁻¹)
  obtain ⟨Dp, hDφ, -⟩ := QDp.exists_bialgEquiv_coe_eq 𝒢 M H S Δ hΔinj d φ ψ hφpts hψpts
  refine ⟨Dp, fun v => ?_, fun v => ?_⟩
  · rw [hDφ, hDφ]
    exact hφt v
  · rw [hDφ]
    exact hφι v

end S_ModularCurve_exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness
end P2MW
export P2MW.S_ModularCurve_exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness (solution)
