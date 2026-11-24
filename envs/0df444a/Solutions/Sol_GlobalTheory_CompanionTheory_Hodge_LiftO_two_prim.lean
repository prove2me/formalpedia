-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.two_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:03.819388+00:00
-- url     : https://prove2.me/submissions/670ff7e1-8d8d-4664-bfa7-fc2e5212db1b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_prim_cochain
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G)
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c) (hC : Closed1 F = ⊤) (f : Z1 F) (β : A0 F)
    (hβ : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ)) (T : E) :
    qOm m 2 T (dOne R _ (β _)) = qOm p 2 T (dOne R _ (β _)) + qOm q 2 T (dOne R _ (β _)) := by
  obtain ⟨g, hg⟩ := exists_prim_cochain m p q hm1 f
  have conn : ∀ (m' : CoefMap (RingHom.id R) F G) {T T' : E} (φ : T ⟶ T'),
      q1 m' T' (β _) = p1 G φ (q1 m' T (β _)) + KaehlerDifferential.D R _ ((m'.pullbackOneCocycle f).1 T T' φ) :=
    fun m' T T' φ ↦ by
      rw [hβ (m'.G.map φ), map_add, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D]; rfl
  let ga : A0 G := fun T ↦ q1 m T (β _) - q1 p T (β _) - q1 q T (β _) - KaehlerDifferential.D R _ (g T)
  have hga : ga ∈ Glob1 G := fun T T' φ ↦ by
    have e := congrArg (KaehlerDifferential.D R (G.obj T')) (hg φ)
    simp only [map_sub, map_add] at e
    simp only [ga, map_sub, p1_D]
    rw [conn m φ, conn p φ, conn q φ, sub_eq_iff_eq_add.1 e]
    abel
  obtain ⟨⟨a, b⟩, hab⟩ := hW.2 ⟨ga, hga⟩
  have hcl : ∀ (a : Glob1 F) (T : C), dOne R _ (a.1 T) = 0 := fun a ↦ by
    have h : a ∈ Closed1 F := by rw [hC]; exact Submodule.mem_top
    exact h
  have e : ga T = q1 p T (a.1 _) + q1 q T (b.1 _) := (congrFun (congrArg Subtype.val hab) T).symm
  have e0 : dOne R _ (ga T) = 0 := by
    rw [e, map_add, ← qOm_dOne, ← qOm_dOne, hcl, hcl, map_zero, map_zero, add_zero]
  simp only [ga, map_sub, dOne_D, sub_zero, ← qOm_dOne] at e0
  rw [sub_sub, sub_eq_zero] at e0
  exact e0
end GlobalTheory.CompanionTheory.Hodge.LiftO
