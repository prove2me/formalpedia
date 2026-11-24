-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeClosed.nu_natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:04.894988+00:00
-- url     : https://prove2.me/submissions/a66e1b84-8e69-46d9-95fb-788c94af87f4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedStOfTwoFormCohSt
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_qOm_wedge
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeClosed
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeClosed
theorem _root_.solution (c : CoefMap (RingHom.id R) F G) (ν : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (ν' : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hν : ∀ a b T, ν (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hν' : ∀ a b T, ν' (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (t : ⋀[R]^2 (Glob1 F)) (T : D) :
    qOm c 2 T (ν t (c.G.obj T)) = ν' (exteriorPower.map 2 (pullGlob1 c) t) T := by
  have e : (qOm c 2 T : _ →ₗ[R] _) ∘ₗ LinearMap.proj (c.G.obj T) ∘ₗ ν =
      LinearMap.proj T ∘ₗ ν' ∘ₗ exteriorPower.map 2 (pullGlob1 c) := by
    apply exteriorPower.linearMap_ext
    ext x
    obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] := ⟨x 0, x 1, by funext i; fin_cases i <;> rfl⟩
    have hy : (pullGlob1 c : Glob1 F →ₗ[R] Glob1 G) ∘ ![a, b] = ![pullGlob1 c a, pullGlob1 c b] := by
      funext i; fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      exteriorPower.map_apply_ιMulti]
    rw [hy, hν, hν']
    exact congrArg Subtype.val (qOm_wedge c (a.1 (c.G.obj T)) (b.1 (c.G.obj T)))
  exact LinearMap.congr_fun e t
end GlobalTheory.CompanionTheory.HodgeClosed
