-- Prove2me | solution 1 for GlobalTheory.UU.GtTors.chain_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:10:59.918492+00:00
-- url     : https://prove2.me/submissions/2492df75-f253-43aa-96ac-9a7e0c1b4be9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU
namespace GtTors
theorem _root_.solution {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) {T : Over (Spec (CommRingCat.of R))}
    (σ : T ⟶ TF (R := R) F) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    1 * cubN (th D z J) k 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hz.2 mu) σ.left).trans (val_one _)).symm rfl
end GtTors
end GlobalTheory.UU
