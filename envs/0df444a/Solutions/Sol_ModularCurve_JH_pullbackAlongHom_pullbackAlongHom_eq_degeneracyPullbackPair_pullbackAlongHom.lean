-- Prove2me | solution 1 for ModularCurve.JH.pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/08fdb03a-2e98-5eab-86a4-90396551f276

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JH_pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom

set_option autoImplicit false

open ModularCurve AlgebraicCurve

namespace DegenCompat

section Generic

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']
  [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F'']

theorem pullbackAlong_congr {φ ψ : F →ₐ[K] F''} (h : φ = ψ)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h; rfl

theorem pullbackAlongHom_pullbackAlongHom_eq_of_comp_eq
    {G : Type*} [Field G] [Algebra K G] [HasPrincipalDivisors K G]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFIφ : FundamentalIdentityAlong K φ hφ)
    (χ : F' →ₐ[K] F'') (hχ : χ.toRingHom.IsIntegral) (hFIχ : FundamentalIdentityAlong K χ hχ)
    (φ' : F →ₐ[K] G) (hφ' : φ'.toRingHom.IsIntegral) (hFIφ' : FundamentalIdentityAlong K φ' hφ')
    (χ' : G →ₐ[K] F'') (hχ' : χ'.toRingHom.IsIntegral) (hFIχ' : FundamentalIdentityAlong K χ' hχ')
    (hsq : χ.comp φ = χ'.comp φ') (x : Pic0 K F) :
    Pic0.pullbackAlongHom χ hχ hFIχ (Pic0.pullbackAlongHom φ hφ hFIφ x) =
      Pic0.pullbackAlongHom χ' hχ' hFIχ' (Pic0.pullbackAlongHom φ' hφ' hFIφ' x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  show Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ (D : Divisor K F)) =
    Divisor.pullbackAlong χ' hχ' (Divisor.pullbackAlong φ' hφ' (D : Divisor K F))
  rw [Divisor.pullbackAlong_pullbackAlong φ χ hφ hχ (RingHom.IsIntegral.trans _ _ hφ hχ) D,
    Divisor.pullbackAlong_pullbackAlong φ' χ' hφ' hχ' (RingHom.IsIntegral.trans _ _ hφ' hχ') D]
  exact pullbackAlong_congr hsq _ _ D

end Generic

end DegenCompat

open DegenCompat in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hdeg : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.JOne.DegeneracyPullbackInputs (M / p) M p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M / p))]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ u, ((ι u : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hιint : ι.toRingHom.IsIntegral)
    (hιFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hιint)
    (ι' : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ]
      ↥(ModularCurve.x1FunctionFieldBar (M / p)))
    (hι' : ∀ u, ((ι' u : ↥(ModularCurve.x1FunctionFieldBar (M / p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hι'int : ι'.toRingHom.IsIntegral)
    (hι'FI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι' hι'int)

    (αH βH : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ]
      ↥(ModularCurve.xHFunctionFieldBar M H))
    (hα : ∀ u, ((αH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u, ((βH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) αH hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) βH hβint) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∀ x : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM),
      AlgebraicCurve.Pic0.pullbackAlongHom ι hιint hιFI (AlgebraicCurve.Pic0.pullbackAlongHom αH hαint hαFI x) =
        ModularCurve.JOne.degeneracyPullbackPair (M / p) M p 0
          (AlgebraicCurve.Pic0.pullbackAlongHom ι' hι'int hι'FI x)) ∧
    (∀ x : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM),
      AlgebraicCurve.Pic0.pullbackAlongHom ι hιint hιFI (AlgebraicCurve.Pic0.pullbackAlongHom βH hβint hβFI x) =
        ModularCurve.JOne.degeneracyPullbackPair (M / p) M p 1
          (AlgebraicCurve.Pic0.pullbackAlongHom ι' hι'int hι'FI x)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨hdvd, hβ1, h₁, h₂, hP, hFI₁, hFI₂⟩ := hdeg

  have hsqα : ι.comp αH = (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right (M / p) p).trans hdvd)).comp ι' := by
    apply AlgHom.ext; intro u; apply Subtype.ext
    show ((ι (αH u) : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right (M / p) p).trans hdvd) (ι' u) : ↥(x1FunctionFieldBar M)) :
        LaurentSeries (AlgebraicClosure ℚ))
    rw [hι, hα, coe_x1LevelInclBar, hι']
  have hsqβ : ι.comp βH = (x1LevelSubstBar (AlgebraicClosure ℚ) p hdvd).comp ι' := by
    apply AlgHom.ext; intro u; apply Subtype.ext
    show ((ι (βH u) : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((x1LevelSubstBar (AlgebraicClosure ℚ) p hdvd (ι' u) : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ))
    rw [hι, hβ, coe_x1LevelSubstBar_of (AlgebraicClosure ℚ) p hdvd hβ1, hι']
  rw [JOne.degeneracyPullbackPair_eq hdvd hβ1 h₁ h₂ hFI₁ hFI₂]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · simp only [Matrix.cons_val_zero]
    exact pullbackAlongHom_pullbackAlongHom_eq_of_comp_eq αH hαint hαFI ι hιint hιFI ι' hι'int hι'FI _ h₁ hFI₁ hsqα x
  · simp only [Matrix.cons_val_one]
    exact pullbackAlongHom_pullbackAlongHom_eq_of_comp_eq βH hβint hβFI ι hιint hιFI ι' hι'int hι'FI _ h₂ hFI₂ hsqβ x

end S_ModularCurve_JH_pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom
end P2MW
export P2MW.S_ModularCurve_JH_pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom (solution)
