-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.txT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:30.479807+00:00
-- url     : https://prove2.me/submissions/76eedfcb-9ac1-43fb-b039-17e622340441

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_mulq_eq
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_pow
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_wQ_eq
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_vt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
namespace GlobalTheory.Ex.NumD.Hom
theorem _root_.solution {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (χ : N.X) : N'.txT m p' (I.e χ) = I.lam * f (N.txT m p χ) := by
  have a := I.wQ_eq hm.pow p p' ep hp
  have b := I.mulq_eq m p.1.2.b
  have key : N'.wQ p' / mulq N'.θ N'.σ m (I.φ p.1.2.b) * (I.lam * I.h (p.1.2.b ^ m)) =
      I.lam * F (N.wQ p / mulq N.θ N.σ m p.1.2.b) := by
    rw [map_div]
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace b := congrArg Additive.ofMul b
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a - b
  rw [txT, txT, (hp.pow m).vt_eq, hp.1, Gt.pow_b, ← mul_assoc, ← Units.val_mul, key, map_mul f, Units.val_mul,
    mul_assoc]
  rfl
end GlobalTheory.Ex.NumD.Hom
