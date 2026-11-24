-- Prove2me | solution 1 for GlobalTheory.CuspCentre.span_zGam_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:00.649463+00:00
-- url     : https://prove2.me/submissions/f7b5c6dd-4700-4b67-a274-402c2eb37fd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SpanCuspCentreArithmeticGroupFg
import Theorems.Thm_GlobalTheory_CuspCentre_displ_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.CuspCentre
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ), (Submodule.span ℤ (FJ.zGam X cu)).FG := by
  intro E _ _ _ r ρ X cu
  obtain ⟨s, hs⟩ := X.Λ_fg
  have hsE : Submodule.span E (s : Set (Fin r → E)) = ⊤ := by
    rw [← X.Λ_span, ← hs, Submodule.span_span_of_tower]
  have hΛ : (X.Λ.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h2 : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact Module.Finite.iff_fg.1 h2
  have hN : (Submodule.pi Set.univ fun _ : s => X.Λ.restrictScalars ℤ).FG :=
    Submodule.fg_pi fun _ => hΛ
  refine Submodule.fg_of_fg_map_injective (displ X cu s).toIntLinearMap
    (displ_injective X cu s hsE) (hN.of_le ?_)
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro β ⟨-, γ, hγ, e⟩ v -
  have hv : v.1 ∈ X.Λ := hs ▸ Submodule.subset_span v.2
  change FJ.zMatE X cu.e β *ᵥ v.1 - v.1 ∈ X.Λ
  rw [← e]
  exact X.Λ.sub_mem (((X.Γ_stab γ hγ).2 _).1 hv) hv
end GlobalTheory.CuspCentre
