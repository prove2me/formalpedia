-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:47.170619+00:00
-- url     : https://prove2.me/submissions/2f143a01-9153-4e78-9fa4-df0ab74c0637

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_exists_finite_chart

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread
namespace GlobalTheory.CompanionTheory.SmoothSpread
theorem _root_.solution : GlobalTheory.SpreadingModels.Spreads (fun _ _ f ↦ Smooth f) := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π ⟨hfg, hlfp, hqc, hqs, hpb⟩ hsm
  letI : Algebra R₀ R := φ.toAlgebra
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  let 𝒰 := Y₀.affineCover.finiteSubcover
  have hch (i : 𝒰.I₀) := exists_finite_chart (R := R) (R₀ := R₀) hlfp hpb hsm (𝒰.f i)
  choose s hs H using hch
  have : Finite 𝒰.I₀ := by
    change Finite Y₀.affineCover.finiteSubcover.I₀
    infer_instance
  let A : Subalgebra R₀ R := Algebra.adjoin R₀ (⋃ i, s i)
  have hAfg : A.FG := ⟨(Set.finite_iUnion hs).toFinset, by simp [A]⟩
  have hft : Algebra.FiniteType R₀ A := (Subalgebra.fg_iff_finiteType A).mp hAfg
  refine ⟨A, inferInstance, algebraMap R₀ A, algebraMap A R, rfl, Algebra.FiniteType.trans hfg hft, ?_⟩
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0})
    (𝒰.pullback₁ (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))))) fun i ↦ ?_
  exact H i A (fun x hx ↦ Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hx⟩))
    ((IsPullback.of_hasPullback _ (𝒰.f i)).flip.paste_vert (IsPullback.of_hasPullback _ _))
end GlobalTheory.CompanionTheory.SmoothSpread
