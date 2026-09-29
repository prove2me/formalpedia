-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2288c0b7-03b0-57e2-a72f-768e782330e4

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (hrange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))

    (hinertF : ∀ (m : ℕ), 0 < m → ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ x ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) m,
        σ • x - x ∈ O.finPts m)

    {hB : ℕ} (ℬ : PDivisibleGroup Rh p hB) (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    (hrefl : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
              algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
              algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hper : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
              algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) :
    ∀ τ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x : TateModule p (ModularCurve.JH M H),
      ∃ y : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e y = ModularCurve.JH.tateGaloisRep M H p τ x - x ∧
        ∀ n : ℕ, ∃ (w : ℕ) (f : 𝒢.Point (AlgebraicClosure ℚ) w),
          𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : 𝒢.level w, Pl.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by
  intro τ hτ x
  have hp : p.Prime := Fact.out

  have hmem : ModularCurve.JH.tateGaloisRep M H p τ x - x ∈ LinearMap.range e := by
    refine (hrange _).2 fun n => ?_
    rw [TateModule.coe_sub, Pi.sub_apply, TateModule.rep_apply]
    refine hinertF (p ^ n) (pow_pos hp.pos n) τ hτ _ ?_
    exact AlgebraicCurve.Pic0.mem_torsion.2 (TateModule.torsion x n)
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, hy, fun n => ?_⟩

  have hex := PDivisibleGroup.Points.exists_mkAdd 𝒢 ((y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n)
  obtain ⟨w, f, hf⟩ := hex
  have hf' : 𝒢.pointsMkAdd (AlgebraicClosure ℚ) (max w n)
      (Additive.ofMul (𝒢.pointInclLE (AlgebraicClosure ℚ) (le_max_left w n) f)) =
        (y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n := by
    rw [PDivisibleGroup.pointsMkAdd_pointInclLE]; exact hf
  refine ⟨max w n, 𝒢.pointInclLE (AlgebraicClosure ℚ) (le_max_left w n) f, hf', ?_⟩

  refine hrefl (max w n) _ (hper (max w n) τ hτ ((x : ℕ → ModularCurve.JH M H) n) ?_ _ ?_)
  ·
    refine AlgebraicCurve.Pic0.mem_torsion.2 ?_
    rw [← Nat.sub_add_cancel (le_max_right w n), pow_add, Nat.cast_mul, mul_smul, TateModule.torsion,
      smul_zero]
  · rw [hf', ← he y n, hy, TateModule.coe_sub, Pi.sub_apply, TateModule.rep_apply]

end S_ModularCurve_JHNeronObjectAtP_exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period (solution)
