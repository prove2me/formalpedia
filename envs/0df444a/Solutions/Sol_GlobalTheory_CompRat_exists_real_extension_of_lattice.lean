-- Prove2me | solution 1 for GlobalTheory.CompRat.exists_real_extension_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:35:56.685112+00:00
-- url     : https://prove2.me/submissions/fec6a097-dad5-4a90-9475-891fc04a81eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsComplexLinearOfPureTypes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CompRat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
namespace GlobalTheory.CompRat
namespace _root_.GlobalTheory.CompRat
theorem _root_.solution {A V W : Type} [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (P : A →+ V) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) (Q : A →+ W) :
    ∃ r : V →ₗ[ℝ] W, ∀ a, r (P a) = Q a := by
  set L : Submodule ℤ V := P.range.toIntSubmodule with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by simpa [hL] using hs⟩
  let b := Module.Free.chooseBasis ℤ L
  let e : A ≃+ P.range := AddMonoidHom.ofInjective hi
  let r : V →ₗ[ℝ] W := (b.ofZLatticeBasis ℝ L).constr ℝ (fun i => Q (e.symm (b i)))
  refine ⟨r, fun a => ?_⟩
  let f₁ : L →+ W := r.toAddMonoidHom.comp L.subtype.toAddMonoidHom
  let f₂ : L →+ W := Q.comp e.symm.toAddMonoidHom
  have hf : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show r (b i : V) = Q (e.symm (b i))
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ L b i]
    exact (b.ofZLatticeBasis ℝ L).constr_basis ℝ (fun i => Q (e.symm (b i))) i
  have h : r (P a) = Q (e.symm ⟨P a, a, rfl⟩) := LinearMap.congr_fun hf ⟨P a, a, rfl⟩
  have he : e.symm ⟨P a, a, rfl⟩ = a := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [h, he]
end _root_.GlobalTheory.CompRat
end GlobalTheory.CompRat
