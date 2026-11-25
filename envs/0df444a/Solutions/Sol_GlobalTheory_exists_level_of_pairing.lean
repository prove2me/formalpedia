-- Prove2me | solution 1 for GlobalTheory.exists_level_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:18.267733+00:00
-- url     : https://prove2.me/submissions/8892b71b-89bc-4ba0-b07d-c33ae62749a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
import Theorems.Thm_GlobalTheory_LevelOfPairing_injective_comb
import Theorems.Thm_GlobalTheory_LevelOfPairing_surjective_comb
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open LevelOfPairing
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → WeilSt → MulNSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), IsPrimitiveRoot ze M → (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S), (M : K) ≠ 0 ∧ IsPrimitiveRoot (Units.map s.appTop.hom.toMonoidHom ze) M) → ∀ x : Fin (2 * P.g) → (baseOver S ⟶ P.A), (∀ i, x i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (x i) (x j) (ze ^ stdSymp P.g i j)) → ∃ lev : Level P M ze, lev.pt = x := by
  intro hG hW hN S _ P M ze hze hK x hx hp
  have := P.isAb.comm
  have cm : ∀ (T : Over S) (a b : T ⟶ P.A), Commute a b := fun T a b => _root_.mul_comm a b
  have tor : ∀ (T : Over S) (h : T ⟶ baseOver S) (i), (h ≫ x i) ^ M = 1 := fun T h i => by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have ind : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (c c' : Fin (2 * P.g) → Fin M),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro K _ s c c' e
    obtain ⟨hu, hm, -⟩ := hW S P M (Over.mk s)
    refine injective_comb (R := fun a b u => WeilIs P.A P.L M a b u) (cm _) hu hm (hK K s).2 _
      (tor _ _) (fun i j => ?_) c c' e
    have h := CommPairing.weilIs_pull hG P.isAb P.isLB
      (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) (hp i j)
    exact (map_zpow (Units.map s.appTop.hom.toMonoidHom) ze _) ▸ h
  refine ⟨⟨x, hze, hx, fun K _ _ s => ind K s, fun K _ _ s z hz => ?_, hp⟩, rfl⟩
  have hM : M ≠ 0 := fun e => (hK K s).1 (by rw [e, Nat.cast_zero])
  exact surjective_comb (cm _) hM _ (tor _ _)
    ((hN S P M (Nat.one_le_iff_ne_zero.2 hM)).2.2.2.2 K s (hK K s).1) (ind K s) z hz
end GlobalTheory
