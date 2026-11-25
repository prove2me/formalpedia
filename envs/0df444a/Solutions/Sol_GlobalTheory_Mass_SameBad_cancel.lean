-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:37.04647+00:00
-- url     : https://prove2.me/submissions/485874df-e340-47b2-a5a1-931091231958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
import Theorems.Thm_GlobalTheory_Mass_SameBad_nondeg_of_PD
import Theorems.Thm_GlobalTheory_Mass_SameBad_ext_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_Mass_LocWitt_Rel_trans
import Theorems.Thm_GlobalTheory_T_witt_extension_totally_definite_hermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (hK : IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {k : W →ₗ⋆[K] W →ₗ[K] K} (hh : PD h) {β : K} (β0 : β ≠ 0)
    (hs : (ext k β).IsSymm) (hp : PD (ext k β)) (hd : Module.finrank K V = Module.finrank K W)
    (φ : (V × K) ≃ₗ[K] (W × K)) (hφ : ∀ x y, ext k β (φ x) (φ y) = ext h β x y) :
    ∃ e : V ≃ₗ[K] W, ∀ x y, k (e x) (e y) = h x y := by
  have u0 : ((0, 1) : W × K) ≠ 0 := by simp
  have w0 : φ (0, 1) ≠ 0 := by simp
  let e1 := LinearEquiv.toSpanNonzeroSingleton K _ _ w0
  let e2 := LinearEquiv.toSpanNonzeroSingleton K _ _ u0
  obtain ⟨g, hg, hg1⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K (W × K) (ext k β) hK hs hp).1 _ _ (e1.symm.trans e2) (by
    intro x y
    obtain ⟨s, rfl⟩ := e1.surjective x
    obtain ⟨t, rfl⟩ := e1.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    simp only [e1, e2, LinearEquiv.toSpanNonzeroSingleton_apply, map_smulₛₗ, LinearMap.smul_apply, hφ]
    simp [ext_apply])
  have hg2 : g (φ (0, 1)) = (0, 1) := by
    have := hg1 (e1 1)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at this
    simpa [e1, e2] using this
  have iso : ∀ x y, ext k β (g (φ x)) (g (φ y)) = ext h β x y := fun x y => (hg _ _).trans (hφ x y)
  have z : ∀ x : V, (g (φ (x, 0))).2 = 0 := fun x => by
    have := iso (0, 1) (x, 0)
    rw [hg2] at this
    simpa [ext_apply, β0] using this
  let f : V →ₗ[K] W := LinearMap.fst K W K ∘ₗ (φ.trans g).toLinearMap ∘ₗ LinearMap.inl K V K
  have hf : ∀ x y, k (f x) (f y) = h x y := fun x y => by
    have := iso (x, 0) (y, 0)
    rw [ext_apply, ext_apply, z y] at this
    simpa [f] using this
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine (nondeg_of_PD h hh).1 x fun y => ?_
    rw [← hf, hx]; simp
  exact ⟨LinearMap.linearEquivOfInjective f inj hd, hf⟩
end GlobalTheory.Mass.SameBad
