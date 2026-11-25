-- Prove2me | solution 1 for GlobalTheory.PairingLevels.Rep.rigid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:55.791792+00:00
-- url     : https://prove2.me/submissions/62a65cac-6253-4c92-90fb-f9cb215f1084

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
import Theorems.Thm_GlobalTheory_PairingLevels_oneGen_isGen
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_ratio
import Theorems.Thm_GlobalTheory_CommutatorPairing_surj_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}
namespace GlobalTheory.PairingLevels
namespace Rep
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {Z : Over S}
    {D : FreeAbelianGroup ((Z ⊗ A).left ⟶ A.left)} {f : ValFam L (Z ⊗ A)} (h : Rep L D f) (hD : D = 0)
    (a : Z ⟶ A) {z : Z.left} {J} (hJ : Good L z J) : f Z (lift (𝟙 Z) a) z J = f Z (lift (𝟙 Z) 1) z J := by
  obtain ⟨K, _, φ, ε, t, ht, hD', hv⟩ := h
  obtain ⟨c, hc⟩ := exists_ratio hL (φ := φ) (ε := ε) (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ g => by
      have := congrArg (FreeAbelianGroup.lift (fun q => Additive.ofMul (g q))) (hD'.trans hD)
      simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of, map_zero] at this
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      apply Additive.ofMul.injective
      simpa only [ofMul_prod, ofMul_zpow, ofMul_one] using this)
    (fst Z A).left (lift (𝟙 Z) 1).left (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA Z) ht oneGen_isGen
  rw [← hv _ _ z J hJ, ← hv _ _ z J hJ, hc _ _ z J hJ, hc _ _ z J hJ, val_one, val_one, ← Over.comp_left,
    ← Over.comp_left, lift_fst, lift_fst]
end Rep
end GlobalTheory.PairingLevels
