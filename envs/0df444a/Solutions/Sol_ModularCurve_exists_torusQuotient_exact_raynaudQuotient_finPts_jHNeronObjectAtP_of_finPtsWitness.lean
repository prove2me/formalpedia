-- Prove2me | solution 1 for ModularCurve.exists_torusQuotient_exact_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ef484886-ae31-5a10-a127-39d183a9955c

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
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_PDivisibleGroup_Tower
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit
import Theorems.Thm_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_torusQuotient_exact_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace QT1Aux

variable {R : Type*} [CommRing R]
variable {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

theorem exists_bialgHom_comp_eq_of_surjective (f : B →ₐc[R] C) (hf : Function.Surjective f) (g : B →ₐc[R] D)
    (hker : RingHom.ker (f : B →+* C) ≤ RingHom.ker (g : B →+* D)) :
    ∃ r : C →ₐc[R] D, r.comp f = g := by
  classical
  let r0 : C →+* D := (f : B →+* C).liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
    ⟨(g : B →+* D), hker⟩
  have hr0 : ∀ b, r0 (f b) = g b := fun b =>
    (f : B →+* C).liftOfRightInverse_comp_apply (Function.surjInv hf) (Function.rightInverse_surjInv hf)
      ⟨(g : B →+* D), hker⟩ b
  let ra : C →ₐ[R] D :=
    { toRingHom := r0
      commutes' := fun c => by
        change r0 (algebraMap R C c) = algebraMap R D c
        rw [← AlgHomClass.commutes f c]
        change r0 (f (algebraMap R B c)) = _
        rw [hr0, AlgHomClass.commutes] }
  have hra : ∀ b, ra (f b) = g b := hr0
  refine ⟨BialgHom.ofAlgHom ra ?_ ?_, ?_⟩
  · apply AlgHom.ext
    intro c
    obtain ⟨b, rfl⟩ := hf c
    change Coalgebra.counit (R := R) (ra (f b)) = Coalgebra.counit (R := R) (f b)
    rw [hra, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  · apply AlgHom.ext
    intro c
    obtain ⟨b, rfl⟩ := hf c
    change Algebra.TensorProduct.map ra ra (Coalgebra.comul (R := R) (f b)) = Coalgebra.comul (R := R) (ra (f b))
    rw [hra, ← CoalgHomClass.map_comp_comul_apply f b, ← CoalgHomClass.map_comp_comul_apply g b,
      ← (Coalgebra.Repr.arbitrary R b).eq, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    change ra (f _) ⊗ₜ[R] ra (f _) = _
    rw [hra, hra]
    rfl
  · apply BialgHom.ext
    intro b
    exact hra b

end QT1Aux

open ModularCurve

open ModularCurve in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

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

    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

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

    (hjB : ∀ v, Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)))
    :
    ∃ (T : ℕ → Type) (_ : ∀ v, CommRing (T v)) (_ : ∀ v, HopfAlgebra (ZMod p) (T v))
        (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (T v)) (_ : ∀ v, Module.Finite (ZMod p) (T v)) (_ : ∀ v, Module.Free (ZMod p) (T v))
      (tT : ∀ v, T (v + 1) →ₐc[ZMod p] T v)
      (πT : ∀ v : ℕ, ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] T v),
      (∀ v, Function.Surjective (tT v)) ∧
      (∀ v, Module.finrank (ZMod p) (T v) = p ^ (v * O.toricRank)) ∧
      (∀ v, RingHom.ker (tT v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (T (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (πT v)) ∧
      (∀ v : ℕ, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (tT v).comp (πT (v + 1))) ∧
      (∀ v : ℕ, RingHom.ker (πT v : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] T v) =
        Ideal.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v) : ZMod p ⊗[Rh] ℬ.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[Rh] ℬ.level v)))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Nontrivial (ZMod p) := inferInstance

  let Bq : ℕ → Type := fun v => ZMod p ⊗[Rh] ℬ.level v
  let Bv : ℕ → Type := fun v => ZMod p ⊗[Rh] 𝒢.level v
  let jB : ∀ v, Bq v →ₐc[ZMod p] Bv v := fun v => Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)
  let tG : ∀ v, Bv (v + 1) →ₐc[ZMod p] Bv v := fun v =>
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)
  let tB : ∀ v, Bq (v + 1) →ₐc[ZMod p] Bq v := fun v =>
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ℬ.transition v)
  have htB : ∀ v, Function.Surjective (tB v) := fun v => (ℬ.baseChange (ZMod p)).transition_surjective v
  have hψt' : ∀ v (x : Bq (v + 1)), tG v (jB (v + 1) x) = jB v (tB v x) := by
    intro v x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c b =>
      change c ⊗ₜ[Rh] 𝒢.transition v (ψ (v + 1) b) = c ⊗ₜ[Rh] ψ v (ℬ.transition v b)
      have := DFunLike.congr_fun (hψt v) b
      rw [BialgHom.comp_apply, BialgHom.comp_apply] at this
      rw [this]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

  let J : ∀ v, Ideal (Bv v) := fun v =>
    Ideal.map (jB v : Bq v →ₐ[ZMod p] Bv v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Bq v)))
  have hJmap : ∀ v, Ideal.map (tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) (J (v + 1)) = J v := by
    intro v
    change Ideal.map ((tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) : Bv (v + 1) →+* Bv v)
        (Ideal.map ((jB (v + 1) : Bq (v + 1) →ₐ[ZMod p] Bv (v + 1)) : Bq (v + 1) →+* Bv (v + 1)) _) =
      Ideal.map ((jB v : Bq v →ₐ[ZMod p] Bv v) : Bq v →+* Bv v) _
    rw [Ideal.map_map]
    have hc : ((tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) : Bv (v + 1) →+* Bv v).comp
        ((jB (v + 1) : Bq (v + 1) →ₐ[ZMod p] Bv (v + 1)) : Bq (v + 1) →+* Bv (v + 1)) =
        ((jB v : Bq v →ₐ[ZMod p] Bv v) : Bq v →+* Bv v).comp ((tB v : Bq (v + 1) →ₐ[ZMod p] Bq v) : Bq (v + 1) →+* Bq v) := by
      exact RingHom.ext fun x => hψt' v x
    rw [hc, ← Ideal.map_map]
    change Ideal.map _ (Ideal.map (tB v : Bq (v + 1) →ₐ[ZMod p] Bq v) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (Bq (v + 1)))) =
      Ideal.map _ (PDivisibleGroup.Hopf.augIdeal (ZMod p) (Bq v))
    rw [PDivisibleGroup.Hopf.map_augIdeal_of_surjective (tB v) (htB v)]

  choose T instCR instHopf πT hπT hkerπ hcoc hfin using fun v =>
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit (jB v)
  haveI : ∀ v, Coalgebra.IsCocomm (ZMod p) (T v) := fun v => hcoc v inferInstance
  haveI : ∀ v, Module.Finite (ZMod p) (T v) := fun v => hfin v inferInstance
  haveI : ∀ v, Module.Free (ZMod p) (T v) := fun v => Module.Free.of_divisionRing _ _
  have hkerπ' : ∀ v, RingHom.ker (πT v : Bv v →ₐ[ZMod p] T v) = J v := fun v => hkerπ v

  have htT : ∀ v, ∃ r : T (v + 1) →ₐc[ZMod p] T v, r.comp (πT (v + 1)) = (πT v).comp (tG v) := by
    intro v
    apply QT1Aux.exists_bialgHom_comp_eq_of_surjective (πT (v + 1)) (hπT (v + 1))
    intro x hx
    change x ∈ RingHom.ker (πT (v + 1) : Bv (v + 1) →ₐ[ZMod p] T (v + 1)) at hx
    rw [hkerπ'] at hx
    change (πT v) (tG v x) = 0
    have : tG v x ∈ J v := by
      rw [← hJmap v]
      exact Ideal.mem_map_of_mem _ hx
    rw [← hkerπ' v] at this
    exact this
  choose tT htTπ using htT
  have htTπ' : ∀ v x, tT v (πT (v + 1) x) = πT v (tG v x) := fun v x => by
    have := DFunLike.congr_fun (htTπ v) x
    rwa [BialgHom.comp_apply, BialgHom.comp_apply] at this
  refine ⟨T, instCR, instHopf, inferInstance, inferInstance, inferInstance, tT, πT, ?_, ?_, ?_, hπT, ?_, ?_⟩
  ·
    intro v c
    obtain ⟨x, rfl⟩ := hπT v c
    obtain ⟨y, rfl⟩ := (𝒢.baseChange (ZMod p)).transition_surjective v x
    exact ⟨πT (v + 1) y, htTπ' v y⟩
  ·
    intro v
    have h1 := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range (ZMod p) (jB v)
    have h2 : Module.finrank (ZMod p) ↥(jB v : Bq v →ₐ[ZMod p] Bv v).range = p ^ (v * hB) := by
      rw [← (LinearEquiv.finrank_eq (AlgEquiv.ofInjective (jB v : Bq v →ₐ[ZMod p] Bv v) (hjB v)).toLinearEquiv)]
      exact (ℬ.baseChange (ZMod p)).finrank_level v
    have h3 : Module.finrank (ZMod p) (Bv v ⧸ J v) = Module.finrank (ZMod p) (T v) := by
      rw [LinearEquiv.finrank_eq ((Ideal.quotientEquivAlgOfEq (ZMod p) (hkerπ' v).symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective (f := (πT v : Bv v →ₐ[ZMod p] T v)) (hπT v))).toLinearEquiv]
    have h4 : Module.finrank (ZMod p) (Bv v) = p ^ (v * h) := (𝒢.baseChange (ZMod p)).finrank_level v
    change Module.finrank (ZMod p) (Bv v) = Module.finrank (ZMod p) (Bv v ⧸ J v) * _ at h1
    rw [h4, h3, h2, hhB, Nat.mul_add, pow_add] at h1
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h1).symm
  ·
    intro v
    have hsurj : Function.Surjective (πT (v + 1) : Bv (v + 1) →ₐ[ZMod p] T (v + 1)) := hπT (v + 1)
    have e1 : RingHom.ker (tT v) = Ideal.map (πT (v + 1) : Bv (v + 1) →ₐ[ZMod p] T (v + 1))
        (Ideal.comap (πT (v + 1) : Bv (v + 1) →ₐ[ZMod p] T (v + 1)) (RingHom.ker (tT v))) :=
      (Ideal.map_comap_of_surjective _ hsurj _).symm
    have e2 : Ideal.comap (πT (v + 1) : Bv (v + 1) →ₐ[ZMod p] T (v + 1)) (RingHom.ker (tT v)) =
        Ideal.comap (tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) (J v) := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← hkerπ' v, RingHom.mem_ker]
      exact Iff.of_eq (congrArg (· = 0) (htTπ' v x))
    have e3 : Ideal.comap (tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) (J v) =
        J (v + 1) ⊔ RingHom.ker (tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) := by
      rw [← hJmap v]
      change Ideal.comap ((tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) : Bv (v + 1) →+* Bv v)
          (Ideal.map ((tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) : Bv (v + 1) →+* Bv v) (J (v + 1))) = _
      rw [Ideal.comap_map_of_surjective ((tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) : Bv (v + 1) →+* Bv v)
        (show Function.Surjective ((tG v : Bv (v + 1) →ₐ[ZMod p] Bv v) : Bv (v + 1) →+* Bv v) from
          (𝒢.baseChange (ZMod p)).transition_surjective v)]
      rfl
    rw [e1, e2, e3, Ideal.map_sup, ← hkerπ' (v + 1), (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl, bot_sup_eq]
    change Ideal.map _ (RingHom.ker ((𝒢.baseChange (ZMod p)).transition v)) = _
    rw [(𝒢.baseChange (ZMod p)).ker_transition v]
    exact PDivisibleGroup.Hopf.map_torsionIdeal_of_surjective (πT (v + 1)) (hπT (v + 1)) (p ^ v)
  ·
    intro v
    exact (htTπ v).symm
  ·
    intro v
    exact hkerπ' v

end S_ModularCurve_exists_torusQuotient_exact_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness
end P2MW
export P2MW.S_ModularCurve_exists_torusQuotient_exact_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness (solution)
