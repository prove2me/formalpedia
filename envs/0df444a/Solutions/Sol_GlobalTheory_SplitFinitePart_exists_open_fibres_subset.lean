-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.exists_open_fibres_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:10:35.316003+00:00
-- url     : https://prove2.me/submissions/adf8fd48-c47a-4020-b5dd-5570e308155c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {P S : Scheme.{0}} (W : S.Opens) (ρ : P ⟶ W.toScheme) [UniversallyClosed ρ]
    (U : P.Opens) (p : S) (hp : p ∈ W) (hU : ∀ y : P, (ρ y).1 = p → y ∈ U) :
    ∃ W' : S.Opens, p ∈ W' ∧ ∀ y : P, (ρ y).1 ∈ W' → y ∈ U := by
  have hc : IsClosed (ρ '' (U : Set P)ᶜ) := ρ.isClosedMap _ U.isOpen.isClosed_compl
  refine ⟨⟨W.ι '' (ρ '' (U : Set P)ᶜ)ᶜ, W.ι.isOpenEmbedding.isOpenMap _ hc.isOpen_compl⟩, ⟨⟨p, hp⟩, ?_, rfl⟩, ?_⟩
  · rintro ⟨y, hy, e⟩
    exact hy (hU y (congrArg Subtype.val e))
  · rintro y ⟨w, hw, e⟩
    by_contra hy
    exact hw ⟨y, hy, Subtype.ext e.symm⟩
end GlobalTheory.SplitFinitePart
