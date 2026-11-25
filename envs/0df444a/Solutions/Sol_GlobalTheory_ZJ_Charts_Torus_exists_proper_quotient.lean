-- Prove2me | solution 1 for GlobalTheory.ZJ.Charts.Torus.exists_proper_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:11.526375+00:00
-- url     : https://prove2.me/submissions/19897914-e3b6-4593-aab3-ebdeddd317b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
import Theorems.Thm_GlobalTheory_ZJ_hasWt_zero_appLE_base
import Theorems.Thm_GlobalTheory_ZJ_Charts_exists_proper_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs
namespace GlobalTheory.ZJ
namespace Charts.Torus
theorem _root_.solution :
    ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∃ (B : Over (Sp K)) (q : H ⟶ B), IsProper B.hom ∧ IsAffineHom q.left ∧ ∃ V : {i // C.wt i = C.c₀} → B.left.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q.left ⁻¹ᵁ V a, Function.Injective (q.left.appLE (V a) (C.W a) h.le).hom ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE (V a) (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hT
  have : Nonempty H.left := ⟨(η : 𝟙_ (Over (Sp K)) ⟶ H).left (⊥ : PrimeSpectrum K)⟩
  obtain ⟨B, p, q, hq, hp, ha, V, hV, h⟩ := C.exists_proper_image H.hom
  refine ⟨Over.mk p, Over.homMk q hq, hp, ha, V, hV, fun a => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h a
  refine ⟨h₁, h₂, h₃, fun u => ⟨fun hu => (h₄ u).2 (hT.gen a u hu), fun hu => ?_⟩⟩
  refine (Subring.closure_le (t := wtZeroSubring i (C.W a))).2 ?_ ((h₄ u).1 hu)
  rintro _ (⟨v, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact hasWt_zero_appLE_base i _ v
  · exact hT.inv a j hj
end Charts.Torus
end GlobalTheory.ZJ
