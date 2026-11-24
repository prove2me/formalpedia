-- Prove2me | solution 1 for GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:03.863477+00:00
-- url     : https://prove2.me/submissions/409df4a7-9772-4129-afa7-420648572595

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsLocalHomExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalHomExtension
namespace GlobalTheory.LocalHomExtension
theorem _root_.solution {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C]
    [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : Valuation.Integers v O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral)
    (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A O := ι.toAlgebra
  let : Algebra A C := ((algebraMap O C).comp ι).toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  have : Algebra.IsIntegral A B := ⟨hint⟩

  let f : B →ₐ[A] C := IsAlgClosed.lift

  have hO : ∀ b : B, ∃ o : O, algebraMap O C o = f b := fun b => by
    have h1 : IsIntegral A (f b) := (Algebra.IsIntegral.isIntegral b).map f
    exact hv.exists_of_le_one (hv.mem_of_integral h1.tower_top)
  choose g hg using hO
  have inj := hv.hom_inj
  let ι' : B →+* O :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => inj (by rw [hg, map_add, map_add, hg, hg]) }
  have hcomp : ι'.comp φ = ι := by
    ext a
    apply inj
    show algebraMap O C (g (φ a)) = algebraMap O C (ι a)
    rw [hg]
    exact f.commutes a
  refine ⟨ι', ?_, hcomp⟩

  have hA : (IsLocalRing.maximalIdeal O).comap ι = IsLocalRing.maximalIdeal A :=
    ((IsLocalRing.local_hom_TFAE ι).out 0 4).mp (inferInstance : IsLocalHom ι)
  have hp : (((IsLocalRing.maximalIdeal O).comap ι').comap (algebraMap A B)).IsMaximal := by
    rw [Ideal.comap_comap, show ι'.comp (algebraMap A B) = ι from hcomp, hA]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hpm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap ((IsLocalRing.maximalIdeal O).comap ι') hp
  exact ((IsLocalRing.local_hom_TFAE ι').out 0 4).mpr (IsLocalRing.eq_maximalIdeal hpm)
end GlobalTheory.LocalHomExtension
