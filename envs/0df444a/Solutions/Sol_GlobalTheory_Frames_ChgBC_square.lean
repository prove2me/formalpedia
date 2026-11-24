-- Prove2me | solution 1 for GlobalTheory.Frames.ChgBC.square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:47.172921+00:00
-- url     : https://prove2.me/submissions/725730e8-5bcb-4de2-a8f9-dc1898a03ea3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeCommBaseChange
import Theorems.Thm_GlobalTheory_Frames_ChgBC_spMap_id
import Theorems.Thm_GlobalTheory_Frames_ChgBC_ppx_le_cov
import Theorems.Thm_GlobalTheory_Frames_ChgBC_scal_pull
import Theorems.Thm_GlobalTheory_Frames_ChgBC_gx_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.ChgBC
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.Frames.ChgBC
theorem _root_.solution {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {y y' : Sp S ⟶ Xo.X}
    {z z' : Sp T ⟶ Xo.X} (pmA : Gx z ⟶ Gx y) (pmB : Gx z' ⟶ Gx y') (pmC : Gx y' ⟶ Gx y) (pm : Gx z' ⟶ Gx z)
    (hsA : pmA ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk z) Xo.univ.t.G).left)
    (hfA : pmA ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk z) Xo.univ.t.G).left ≫ spMap φ)
    (hsB : pmB ≫ (snd (Over.mk y') Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hfB : pmB ≫ (fst (Over.mk y') Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap φ)
    (hsC : pmC ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk y') Xo.univ.t.G).left)
    (hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left ≫ spMap (RingHom.id S))
    (hs : pm ≫ (snd (Over.mk z) Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap (RingHom.id T))
    (sy : LB.Sec (PPx y)) (sy' : LB.Sec (PPx y')) (sz : LB.Sec (PPx z))
    (haA : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z).U i ≤ pmA ⁻¹ᵁ (PPx y).U i),
      (pmA.appLE _ _ h).hom (sy.f i) = sz.f i)
    (haC : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y').U i ≤ pmC ⁻¹ᵁ (PPx y).U i),
      (pmC.appLE _ _ h).hom (scal y a i * sy.f i) = sy'.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z').U i ≤ pm ⁻¹ᵁ (PPx z).U i)
    (hB : (PPx z').U i ≤ pmB ⁻¹ᵁ (PPx y').U i) :
    (pm.appLE _ _ h).hom (scal z (φ a) i * sz.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
  rw [spMap_id] at hfC hf
  replace hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left :=
    hfC.trans (Category.comp_id _)
  replace hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left :=
    hf.trans (Category.comp_id _)
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply gx_ext
    · rw [Category.assoc, hsA, hs, Category.assoc, hsC, hsB]
    · rw [Category.assoc, hfA, Category.assoc, hfC]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap φ) hf)).trans hfB.symm
  have hA := ppx_le_cov pmA hsA i
  have hC := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z' ⟶ Gx y), q = pmB ≫ pmC → ∀ hh : (PPx z').U i ≤ q ⁻¹ᵁ (PPx y).U i,
      (q.appLE _ _ hh).hom (scal y a i * sy.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC ≫ pmB.appLE _ _ hB :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC hB).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC]
  rw [← haA i hA, ← scal_pull φ pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y a i * sy.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _
end GlobalTheory.Frames.ChgBC
