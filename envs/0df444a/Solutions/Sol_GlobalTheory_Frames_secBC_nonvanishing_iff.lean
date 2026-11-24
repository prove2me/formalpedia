-- Prove2me | solution 1 for GlobalTheory.Frames.secBC_nonvanishing_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:47.89437+00:00
-- url     : https://prove2.me/submissions/2fed7d96-290a-4796-832d-fb93d74cd2e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionNonvanishingIff
import Theorems.Thm_GlobalTheory_Frames_exists_mem_basicOpen_iff_of_isPullback

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
open GlobalTheory GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x x' hx s s' hbc p'
  obtain ⟨pm, h1, h2, h3⟩ := hbc
  have hA : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left
      Xo.univ.t.G.hom x := (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have hB : IsPullback (snd (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
      Xo.univ.t.G.hom x' := (IsPullback.of_hasPullback x' Xo.univ.t.G.hom).flip
  have hP : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) := by
    refine IsPullback.of_right ?_ h2 hA
    rw [h1]
    exact hx ▸ hB
  have hU : ∀ i : Fin 1 → Xo.univ.t.PP.L.ι, (PPx x').U i = pm ⁻¹ᵁ (PPx x).U i := by
    intro i
    ext y
    change y ∈ ⋂ k : Fin 1, (snd (Over.mk x') Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) ↔
      pm y ∈ ⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
    rw [← h1]
    simp only [Set.mem_iInter, Set.mem_preimage, Scheme.Hom.comp_apply]
  have h1' : ∀ i, scal x 1 i = 1 := fun i => by
    simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]
  refine exists_mem_basicOpen_iff_of_isPullback hP (PPx x).U (PPx x').U hU s.f s'.f (fun i => ?_) p'
  have := h3 i (hU i).le
  rwa [h1' i, _root_.one_mul] at this
end GlobalTheory.Frames
