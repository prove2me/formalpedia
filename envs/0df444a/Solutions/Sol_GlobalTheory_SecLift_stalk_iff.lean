-- Prove2me | solution 1 for GlobalTheory.SecLift.stalk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:25.750483+00:00
-- url     : https://prove2.me/submissions/8b8f0e86-6737-4db9-9a2f-6b7d56619560

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_GlobalTheory_SecLift_inducing_of_surj
import Theorems.Thm_GlobalTheory_SecLift_exists_affine_zero
import Theorems.Thm_GlobalTheory_SecLift_stalkMap_gr
import Theorems.Thm_P2M_GlobalTheory_SecLift_mem_of_flat__d784d2797ad4
import Theorems.Thm_GlobalTheory_SmallExtLift_app_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_cst_flat
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_app_eq_zero
import Theorems.Thm_GlobalTheory_SmallExtLift_mul_eq_zero_of_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution {A₀ : Type} [CommRing A₀] {g : A →+* A₀} (hg : Function.Surjective g) {a : A}
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g) {f : X ⟶ Spec (CommRingCat.of A)} [Flat f]
    {j : Y ⟶ X} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)}
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g))) (y : Y)
    (e : X.presheaf.stalk (j y)) :
    cstS (𝟙 X ≫ f) (j y) a * e = 0 ↔ (j.stalkMap y).hom e = 0 := by
  obtain ⟨U, h, s, rfl⟩ := X.presheaf.exists_germ_eq e
  change _ * gr (𝟙 X) (j y) U h s = 0 ↔ (j.stalkMap y).hom (gr (𝟙 X) (j y) U h s) = 0
  rw [stalkMap_gr]
  constructor
  · intro H
    rw [← gr_cst (𝟙 X) f (j y) U h, ← map_mul] at H
    obtain ⟨V, hle, hV, hy, e⟩ := exists_affine_zero (F := 𝟙 X) Topology.IsInducing.id (j y) U h _ H
    have e' : cst f V a * rs X hle s = 0 := gr_ext fun x hx => by
      have := congrArg (gr (𝟙 X) x V hx) (show rs X hle (cst f U a * s) = 0 from e)
      rw [gr_res, map_mul, gr_cst] at this
      rw [map_mul, gr_res, gr_cst, this]
    have hm := mem_of_flat' (fun x => (ha x).1) _ (cst_flat f hV) _ e'
    have e₀ : (j.app V).hom (rs X hle s) = 0 := by
      refine (show _ ≤ RingHom.ker (j.app V).hom from Ideal.map_le_iff_le_comap.2 fun r hr => ?_) hm
      rw [Ideal.mem_comap, RingHom.mem_ker, app_cst P.w, (RingHom.mem_ker).1 hr, map_zero]
    rw [← gr_res (𝟙 Y ≫ j) y hle hy, ← gr_app (𝟙 Y) j y V hy, e₀, map_zero]
  · intro H
    obtain ⟨V, hle, hV, hy, e⟩ := exists_affine_zero (inducing_of_surj hg P) y U h s H
    have := mul_eq_zero_of_mem (cst f V) (ε := a) (fun x hx => by rw [mul_comm]; exact (ha x).2 hx)
      (mem_of_app_eq_zero hg P hV _ e)
    rw [← gr_res (𝟙 X) (j y) hle hy, ← gr_cst (𝟙 X) f (j y) V hy, ← map_mul, this, map_zero]
end GlobalTheory.SecLift
