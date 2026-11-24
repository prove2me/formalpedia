-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.loc_of_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:16.82868+00:00
-- url     : https://prove2.me/submissions/23db573f-f594-4b57-9e8e-71cf933d9801

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_sec_ext
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_sec_ratio
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_loc_smul
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_exists_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_linComb_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
variable {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M)
variable {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
  (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
include h
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution (hM : M.IsLB) (H : Triv (M.pull π)) : ∃ v : Fin P.a → R', (P.D₀.map g).mulVec v = 0 ∧
    (∀ i, IsUnit (loc P π f' v i)) ∧ (Function.Surjective f'.appTop.hom →
      ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : R', w = c • v) := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  obtain ⟨t, ht⟩ := H
  let s : LB.Sec (M.pull π) := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  obtain ⟨v, hv⟩ := E.surjective s
  have e : ∀ i, loc P π f' v.1 i = rs X' (le_pull M π (P.le i)) (t.s fun _ => P.ch i).val := fun i => by
    refine (hE v i).symm.trans ?_
    rw [hv]
  refine ⟨v.1, v.2, fun i => by rw [e]; exact (Units.isUnit _).map _, fun hs w hw => ?_⟩
  obtain ⟨ρ, hρ⟩ := sec_ratio (TLinPf.linComb_cover M hM _ _) (E ⟨w, hw⟩) t ht
  obtain ⟨c', rfl⟩ := hs ρ
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c'
  have hc : (P.D₀.map g).mulVec (c • v.1) = 0 := by rw [Matrix.mulVec_smul, v.2, smul_zero]
  refine ⟨c, congrArg Subtype.val (E.injective (a₁ := ⟨w, hw⟩) (a₂ := ⟨c • v.1, hc⟩) ?_)⟩
  refine sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i))
    (fun y => exists_mem P (π y)) fun i => ?_
  refine Eq.trans ?_ ((hE ⟨c • v.1, hc⟩ i).trans (loc_smul P π f' c v.1 i)).symm
  exact (congrArg _ (hρ _)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (rs_rs _ _ _) (e i).symm))
end GlobalTheory.AbLaw.Seesaw
