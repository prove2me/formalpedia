-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:49.063806+00:00
-- url     : https://prove2.me/submissions/8fbd38b0-c0e7-408b-a853-9fd883fec91d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralUnramifiedExtIffIsIntegralBase
import Theorems.Thm_GlobalTheory_T_exists_integer_spanning_family_of_unramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (a : B.A) : @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  classical
  choose ι hι using fun c => exists_int_image hU c
  have inj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
  let f : K.O →+* K'.O :=
    { toFun := ι
      map_one' := inj (by rw [hι]; simp)
      map_mul' := fun x y => inj (by simp [hι])
      map_zero' := inj (by rw [hι]; simp)
      map_add' := fun x y => inj (by simp [hι]) }
  have hf : ∀ c, algebraMap K'.O K'.E (f c) = φ (algebraMap K.O K.E c) := hι
  letI : Algebra K.O K'.O := f.toAlgebra
  letI iC : Algebra K'.O B.A := (overExt φ B ψ hψ hσ).aO
  have hC : ∀ y : K'.O, algebraMap K'.O B.A y = ψ (algebraMap K'.O K'.E y) := fun _ => rfl
  haveI : IsScalarTower K.O K'.O B.A := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A c, RingHom.algebraMap_toAlgebra, hC]
    show _ = ψ (algebraMap K'.O K'.E (f c))
    rw [hf, hψ]
  show IsIntegral K'.O a ↔ IsIntegral K.O a
  constructor
  · intro h
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU
    haveI : Module.Finite K.O K'.O := by
      refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
      obtain ⟨c, hc⟩ := hu y
      have hy : y = ∑ i, c i • u i := by
        apply inj
        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
      rw [hy]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp
    haveI : Algebra.IsIntegral K.O K'.O := Algebra.IsIntegral.of_finite K.O K'.O
    exact isIntegral_trans (R := K.O) (A := K'.O) a h
  · intro h
    exact h.tower_top
end GlobalTheory.UnitLemma.Unr
