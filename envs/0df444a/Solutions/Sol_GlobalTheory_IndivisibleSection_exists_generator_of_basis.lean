-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.exists_generator_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:25:42.0966+00:00
-- url     : https://prove2.me/submissions/337d87d6-f970-483f-b278-a359dd24a389

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_GlobalTheory_IndivisibleSection_exists_generator_of_iso

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndivisibleSection
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.IndivisibleSection
theorem _root_.solution (q : Sp R ⟶ Sp R) (hq : q = 𝟙 _)
    (β : LB.Sec (LPow D.P.A D.P.L (1 : ℕ) (Over.mk q)))
    (hli : ∀ r : Γ((Over.mk q).left, ⊤), r • (SecM.ofSec D.P.A β : SecM D.P.A D.P.L (1 : ℕ) (Over.mk q)) = 0 → r = 0)
    (hsp : ∀ s : SecM D.P.A D.P.L (1 : ℕ) (Over.mk q), ∃ r : Γ((Over.mk q).left, ⊤), r • SecM.ofSec D.P.A β = s) :
    ∃ b : D.SecB 1 0, ∀ s : D.SecB 1 0, ∃! a : R, SecIsMul D.P.A.hom a s b := by
  subst hq
  have hw : (snd (Over.mk (𝟙 (Sp R))) D.P.A).left ≫ D.P.A.hom = (fst (Over.mk (𝟙 (Sp R))) D.P.A).left := by
    have w1 := Over.w (fst (Over.mk (𝟙 (Sp R))) D.P.A)
    have w2 := Over.w (snd (Over.mk (𝟙 (Sp R))) D.P.A)
    simp only [Over.mk_hom] at w1
    rw [w2, ← w1]
    simp
  let u : D.P.A ⟶ Over.mk (𝟙 (Sp R)) := Over.homMk D.P.A.hom (by simp)
  have h₁ : (lift u (𝟙 D.P.A)).left ≫ (snd (Over.mk (𝟙 (Sp R))) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]
    rfl
  have h₂ : (snd (Over.mk (𝟙 (Sp R))) D.P.A).left ≫ (lift u (𝟙 D.P.A)).left = 𝟙 _ := by
    rw [← Over.comp_left]
    have e : snd (Over.mk (𝟙 (Sp R))) D.P.A ≫ lift u (𝟙 D.P.A) = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp]
        ext
        simp only [Over.comp_left, u, Over.homMk_left]
        exact hw
      · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
    rw [e]
    rfl
  refine exists_generator_of_iso D (snd (Over.mk (𝟙 (Sp R))) D.P.A).left (lift u (𝟙 D.P.A)).left h₁ h₂ _ rfl β ?_
  intro s
  obtain ⟨r, hr⟩ := hsp (SecM.ofSec D.P.A (s : (LPow D.P.A D.P.L (↑(1 : ℕ)) (Over.mk (𝟙 (Sp R)))).Sec))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, ?_, fun a' ha' => ?_⟩
  · unfold SecIsMul
    intro j
    have hj := congrArg (fun x => x.1 j) hr
    change r • β.f j = s.f j at hj
    rw [← hj, hw]
    unfold resTop scal
    simp only [Iso.hom_inv_id_apply]
    rfl
  · obtain ⟨r', hr'⟩ : ∃ r' : Γ((Over.mk (𝟙 (Sp R))).left, ⊤),
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a' = r' := ⟨_, rfl⟩
    have hs' : r' • SecM.ofSec D.P.A β =
        SecM.ofSec D.P.A (s : (LPow D.P.A D.P.L (↑(1 : ℕ)) (Over.mk (𝟙 (Sp R)))).Sec) := by
      apply Subtype.ext
      funext j
      simp only [Submodule.coe_smul, Pi.smul_apply]
      change r' • β.f j = s.f j
      rw [ha' j, hw, ← hr']
      rfl
    have h0 := hli (r' - r) (by rw [sub_smul, hs', hr, sub_self])
    rw [sub_eq_zero] at h0
    rw [← h0, ← hr']
    simp only [Iso.inv_hom_id_apply]
end GlobalTheory.IndivisibleSection
