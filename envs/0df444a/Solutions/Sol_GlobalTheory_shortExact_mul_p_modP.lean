-- Prove2me | solution 1 for GlobalTheory.shortExact_mul_p_modP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:36.842384+00:00
-- url     : https://prove2.me/submissions/dc3c42d4-7957-4217-89b4-5c89f22bcf7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
import Theorems.Thm_GlobalTheory_unit_surjective_zmod
import Theorems.Thm_GlobalTheory_unit_kernel_zmod
import Theorems.Thm_GlobalTheory_unit_pmul_zmod
import Theorems.Thm_GlobalTheory_pmul_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) →
      ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0),
        (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by
  intro C p _ hinj
  let π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C) :=
    { f := fun n => (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app (C.X n)
      comm' := fun i j _ =>
        ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.naturality (C.d i j)) }
  have hz : ((p : ℤ) • 𝟙 C) ≫ π = 0 := by
    ext n x
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f,
      ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_id, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact unit_pmul_zmod p (C.X n) x
  refine ⟨π, hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_zsmul,
      ModuleCat.hom_id] at hy ⊢
    exact unit_kernel_zmod p (C.X n) y hy
  · rw [ModuleCat.mono_iff_injective]
    exact pmul_injective p (C.X n) (hinj n)
  · rw [ModuleCat.epi_iff_surjective]
    exact unit_surjective_zmod p (C.X n)
end GlobalTheory
