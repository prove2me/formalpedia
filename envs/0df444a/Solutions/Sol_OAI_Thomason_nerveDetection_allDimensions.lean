-- Prove2me | solution 1 for OAI.Thomason.nerveDetection_allDimensions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:48:24.114995+00:00
-- url     : https://prove2.me/submissions/5d04d160-ad53-4324-8daf-42a51a8e2340

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T004

section
-- module Solutions.OAIQ043_TH.Thomason_ExtensionAnodyne
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.oneFiberFinite_preservesColimits _root_.OAI.Thomason.OmegaCategory.opFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.zeroFiberFinite_preservesColimits _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetFinite_preservesFilteredColimits _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension Anodyne. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory

lemma thomasonWeak_iff_nerve {C D : OmegaCategory.{u}} (f : C ⟶ D) :
    simplicialWeakEquivalences (thomasonRight.map f) ↔
      simplicialWeakEquivalences (streetNerveFunctor.map f) :=
  exSquared_map_weak_iff _

lemma thomasonWeakFinite_iff_nerve {n : ℕ} {C D : OmegaCategory.NCategory.{u} n} (f : C ⟶ D) :
    simplicialWeakEquivalences ((thomasonRightFinite n).map f) ↔
      simplicialWeakEquivalences ((streetNerveFinite n).map f) :=
  exSquared_map_weak_iff _

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_DimensionOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension One. -/

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

attribute [instance] PosetAttachment.order

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z
open CategoryTheory Limits MorphismProperty

namespace Thomason

theorem nerveDetection_allDimensions_oai :
    thomasonWeakEquivalences.{u} =
      simplicialWeakEquivalences.inverseImage streetNerveFunctor ∧
    ∀ n : ℕ, thomasonWeakEquivalencesFinite.{u} n =
      simplicialWeakEquivalences.inverseImage (streetNerveFinite n) := by
  constructor
  · funext X Y f
    exact propext (Subdivision.thomasonWeak_iff_nerve f)
  · intro n
    funext X Y f
    exact propext (Subdivision.thomasonWeakFinite_iff_nerve f)

end Thomason

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Thomason.nerveDetection_allDimensions_oai.{u} := @OAI.Thomason.nerveDetection_allDimensions_oai.{u}
