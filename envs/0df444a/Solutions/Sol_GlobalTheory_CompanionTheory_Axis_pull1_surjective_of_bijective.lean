-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.pull1_surjective_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:02.65058+00:00
-- url     : https://prove2.me/submissions/d8019f09-0489-4200-a794-0a04000056cd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : (Bx P)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (m : CoefMap (RingHom.id R) (box F) F') (hG : m.G = boxG P) (hb : ∀ T, Function.Bijective (m.α T)) :
    Function.Surjective m.pull1 := by
  obtain ⟨G, α, nat, sm⟩ := m
  obtain rfl : G = boxG P := hG
  intro c
  obtain ⟨f', rfl⟩ := H1.mk_surjective _ c
  let e : ∀ T, (box F).obj ((boxG P).obj T) ≃+* F'.obj T := fun T ↦ RingEquiv.ofBijective (α T) (hb T)
  have he : ∀ T x, α T ((e T).symm x) = x := fun T x ↦ (e T).apply_symm_apply x
  let f : C1 (box F) := fun T T' φ ↦ (e ((boxGi P).obj T')).symm (f'.1 _ _ ((boxGi P).map φ))
  have hf : f ∈ Z1 (box F) := by
    intro T T' T'' φ ψ
    refine (hb ((boxGi P).obj T'')).1 ?_
    have h1 : α ((boxGi P).obj T'') (f T T'' (φ ≫ ψ)) = f'.1 _ _ ((boxGi P).map (φ ≫ ψ)) := he _ _
    have h2 : α ((boxGi P).obj T') (f T T' φ) = f'.1 _ _ ((boxGi P).map φ) := he _ _
    have h3 : α ((boxGi P).obj T'') (f T' T'' ψ) = f'.1 _ _ ((boxGi P).map ψ) := he _ _
    have n : α ((boxGi P).obj T'') (mp (box F) ψ (f T T' φ)) =
        mp F' ((boxGi P).map ψ) (α ((boxGi P).obj T') (f T T' φ)) := nat ((boxGi P).map ψ) (f T T' φ)
    refine h1.trans ?_
    refine Eq.trans ?_ (map_add (α ((boxGi P).obj T'')) (mp (box F) ψ (f T T' φ)) (f T' T'' ψ)).symm
    have c : f'.1 _ _ ((boxGi P).map (φ ≫ ψ)) = mp F' ((boxGi P).map ψ) (f'.1 _ _ ((boxGi P).map φ)) +
        f'.1 _ _ ((boxGi P).map ψ) := by
      rw [Functor.map_comp]; exact f'.2 _ _
    exact c.trans (congrArg₂ (· + ·) ((congrArg (mp F' ((boxGi P).map ψ)) h2.symm).trans n.symm) h3.symm)
  refine ⟨H1.mk _ ⟨f, hf⟩, ?_⟩
  refine congrArg (H1.mk F') (Subtype.ext ?_)
  funext T T' φ
  exact he T' _
end GlobalTheory.CompanionTheory.Axis
