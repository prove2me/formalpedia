-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.kaehler_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:20.192942+00:00
-- url     : https://prove2.me/submissions/d13f90a8-8a74-401a-9d71-62a634dcb9f7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_tensor_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_one_tmul_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Cris_Thick_Hom_mem
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution {R' A C N : Type} [CommRing R'] [CommRing A] [CommRing C] [Algebra C A]
    [Algebra A R'] [AddCommGroup N] [Module R' N]
    {f g : (R' ⊗[A] KaehlerDifferential C A) →ₗ[R'] N}
    (h : ∀ a, f (1 ⊗ₜ KaehlerDifferential.D C A a) = g (1 ⊗ₜ KaehlerDifferential.D C A a)) :
    f = g := by
  have key : ∀ x ∈ Submodule.span A (Set.range (KaehlerDifferential.D C A)),
      f (1 ⊗ₜ x) = g (1 ⊗ₜ x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
    | zero => simp
    | add x y _ _ hx hy => simp [TensorProduct.tmul_add, hx, hy]
    | smul a x _ hx =>
      rw [one_tmul_smul, map_smul, map_smul, hx]
  refine tensor_ext fun x => key x ?_
  rw [KaehlerDifferential.span_range_derivation]
  trivial
end GlobalTheory.CompanionTheory.CotLoc
