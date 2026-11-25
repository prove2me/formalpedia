-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:45.309685+00:00
-- url     : https://prove2.me/submissions/f18b994a-dbb1-442c-bc49-9a250b892e3e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_psi_single_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_exists_family
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_simpleIffIrr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory.CompanionTheory.ProdSimple
namespace GlobalTheory.CompanionTheory.ProdSimple
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.ProdSimpleAll := by
  intro s L _ _ W _ _ _ _ ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨x, hx, hne⟩ := exists_family ρ v hv
  choose N h hirr hmem using hx
  have hfin : ∀ c, Module.Finite ℂ (N c) := fun c => inferInstance
  let lam : ∀ c, FDRep ℂ (L c) := fun c => FDRep.of (regSub (N c) (h c))
  let M : MultilinearMap ℂ (fun c => (lam c : Type)) W :=
    (psi ρ v).compLinearMap (fun c => (N c).subtype)
  refine ⟨lam, PiTensorProduct.lift M, fun c => ?_, ?_, fun g => ?_⟩
  · exact (GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 (L c) (lam c)).2 (hirr c)
  · intro h0
    apply hne
    have := congrArg (fun f => f (PiTensorProduct.tprod ℂ (fun c => (⟨x c, hmem c⟩ : N c)))) h0
    simp only [LinearMap.zero_apply, PiTensorProduct.lift.tprod] at this
    exact this
  · apply PiTensorProduct.ext
    ext y
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      PiTensorProduct.lift.tprod]
    exact psi_single_mul ρ v g (fun c => (y c : MonoidAlgebra ℂ (L c)))
end GlobalTheory.CompanionTheory.ProdSimple
