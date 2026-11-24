-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotKer.mul_eq_zero_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:32.335083+00:00
-- url     : https://prove2.me/submissions/f1be7180-f5e9-4ce2-9b71-c9088ab2d502

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
import Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_ker_sq_eq_bot
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotKer
namespace GlobalTheory.CompanionTheory.CotKer
theorem _root_.solution {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (W : (Sp Q).affineOpens) (a b : Γ(Sp Q, W.1))
    (ha : ((spMap q).app W.1).hom a = 0) (hb : ((spMap q).app W.1).hom b = 0) : a * b = 0 := by
  have h := congrArg (fun I => Scheme.IdealSheafData.ideal I W) (ker_sq_eq_bot q hq)
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply, Scheme.Hom.ker_apply] at h
  have hab : a * b ∈ (RingHom.ker ((spMap q).app W.1).hom) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [h] at hab
  exact (Submodule.mem_bot _).mp hab
end GlobalTheory.CompanionTheory.CotKer
