-- Prove2me | solution 1 for GlobalTheory.Conv.exists_halfRing_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:54.112112+00:00
-- url     : https://prove2.me/submissions/ea01165f-31f0-4e94-b7bf-b00faee1b194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_valR_spMap_top
import Theorems.Thm_GlobalTheory_Conv_exists_point_of_ringHom
import Theorems.Thm_GlobalTheory_Conv_exists_factor_halfRing_over
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_point_ext
import Theorems.Thm_GlobalTheory_HolHom_valR_appLE
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {O : Type} [CommRing O] (s : Z ⟶ Sp O) [LocallyOfFiniteType s]
    (b : O →+* ℂ) (y : Sp convLaurent ⟶ Z)
    (hy : y ≫ s = spMap ((algebraMap ℂ convLaurent).comp b)) {V : Z.Opens} (hV : IsAffineOpen V)
    (hyV : ⊤ ≤ y ⁻¹ᵁ V) (T₀ : ℝ) :
    ∃ T ≥ T₀, ∃ yT : Sp (halfRing T) ⟶ Z, ⊤ ≤ yT ⁻¹ᵁ V ∧
      spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y ∧
      yT ≫ s = spMap ((algebraMap ℂ (halfRing T)).comp b) := by
  let ρ : O →+* Γ(Z, V) :=
    (s.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hρ : ρ.FiniteType := by
    refine (s.finiteType_appLE (isAffineOpen_top _) hV le_top).comp (RingHom.FiniteType.of_surjective _ ?_)
    exact (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.surjective
  have hval : ∀ {A : Type} [CommRing A] (x : Sp A ⟶ Z), ⊤ ≤ x ⁻¹ᵁ V → ∀ a : O,
      valR x V (ρ a) = valR (x ≫ s) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) :=
    fun x hx a => valR_appLE x s ⊤ V le_top _ hx
  letI := ρ.toAlgebra
  haveI : Algebra.FiniteType O Γ(Z, V) := hρ
  obtain ⟨T, hT, ψ, hψ, hψb⟩ := exists_factor_halfRing_over (S := O) b (evalHom y V hyV)
    (RingHom.ext fun a => by
      have := hval y hyV a
      rw [hy, valR_spMap_top, valR_eq _ _ hyV] at this
      exact this) T₀
  obtain ⟨yT, hyT, hv⟩ := exists_point_of_ringHom hV ψ
  refine ⟨T, hT, yT, hyT, ?_, ?_⟩
  · refine point_ext hV (fun p _ => hyT (x := spMap _ p) trivial) hyV fun f => ?_
    rw [valR_spMap _ _ _ hyT, hv, valR_eq _ _ hyV, ← hψ]
    rfl
  · refine point_ext (isAffineOpen_top _) le_top le_top fun f => ?_
    obtain ⟨a, rfl⟩ :=
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.surjective f
    have := hval yT hyT a
    rw [hv] at this
    exact this.symm.trans ((DFunLike.congr_fun hψb a).trans (valR_spMap_top _ a).symm)
end GlobalTheory.Conv
