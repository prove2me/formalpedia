-- Prove2me | solution 1 for GlobalTheory.ZV.TorsBasis.of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:25.43734+00:00
-- url     : https://prove2.me/submissions/a219bc10-e11c-4029-b940-46fc1a25b660

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
namespace GlobalTheory.ZV
namespace TorsBasis
theorem _root_.solution [IsAlgClosed K] (P : Out.PolAV (Sp K)) {k : ℕ} (hk : 0 < k) {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P k ze) : TorsBasis P.A k lev.pt := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have e : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
    ext; rfl
  refine ⟨hk, lev.torsion, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) y hy
  have hi := lev.indep K (𝟙 _)
  simp only [e, Category.id_comp] at hc hi
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun d hd => ?_⟩
  · simpa only [ZMod.val_cast_of_lt (c _).2] using hc
  · have := hi (fun i => ⟨(d i).val, ZMod.val_lt _⟩) c (hd.trans hc.symm)
    funext i
    rw [← this]
    simp
end TorsBasis
end GlobalTheory.ZV
