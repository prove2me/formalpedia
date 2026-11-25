-- Prove2me | solution 1 for GlobalTheory.AdaptedBasis.exists_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:10:04.947545+00:00
-- url     : https://prove2.me/submissions/8b25b6ae-1ffb-4f08-b6a9-cfde74e409ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSumSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAdaptedLieBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.AdaptedBasis
private theorem isSemisimple_ringOfIntegers_action {E K V : Type} [Field E] [NumberField E] [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (r : 𝓞 E →+* Module.End K V) (a : 𝓞 E) : (r a).IsSemisimple := by
  have hi : IsIntegral ℤ a := RingOfIntegers.isIntegral a
  have hq : minpoly ℚ (algebraMap (𝓞 E) E a) = (minpoly ℤ a).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ E hi
  have hsep : (minpoly ℚ (algebraMap (𝓞 E) E a)).Separable := Algebra.IsSeparable.isSeparable ℚ _
  rw [hq] at hsep
  have hK := hsep.map (f := algebraMap ℚ K)
  rw [Polynomial.map_map,
    show (algebraMap ℚ K).comp (algebraMap ℤ ℚ) = algebraMap ℤ K from RingHom.ext_int _ _] at hK
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hK.squarefree ?_
  rw [Polynomial.aeval_map_algebraMap]
  have hz := Polynomial.aeval_algHom_apply r.toIntAlgHom a (minpoly ℤ a)
  rw [minpoly.aeval, map_zero] at hz
  exact hz
private theorem exists_ringHom_eq_eigenvalue {R K V : Type} [CommRing R] [Field K] [AddCommGroup V] [Module K V]
    (r : R →+* Module.End K V) {v : V} (hv : v ≠ 0) (χ : R → K) (h : ∀ a, r a v = χ a • v) :
    ∃ t : R →+* K, ∀ a, t a = χ a := by
  have inj : Function.Injective fun c : K => c • v := smul_left_injective K hv
  refine ⟨{ toFun := χ
            map_one' := inj ?_
            map_mul' := fun a b => inj ?_
            map_zero' := inj ?_
            map_add' := fun a b => inj ?_ }, fun _ => rfl⟩
  · show χ 1 • v = (1 : K) • v
    rw [← h, map_one, Module.End.one_apply, one_smul]
  · show χ (a * b) • v = (χ a * χ b) • v
    rw [← h, map_mul, Module.End.mul_apply, h b, map_smul, h a, smul_smul, mul_comm]
  · show χ 0 • v = (0 : K) • v
    rw [← h, map_zero, LinearMap.zero_apply, zero_smul]
  · show χ (a + b) • v = (χ a + χ b) • v
    rw [← h, map_add, LinearMap.add_apply, h a, h b, add_smul]
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap IsUnivChart)
variable {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
end GlobalTheory.AdaptedBasis
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.AdaptedBasis
namespace GlobalTheory.AdaptedBasis
theorem _root_.solution {E K V : Type} [Field E] [NumberField E] [Field K] [IsAlgClosed K] [CharZero K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (r : 𝓞 E →+* Module.End K V) :
    ∃ (g : ℕ) (b : Module.Basis (Fin g) K V) (ty : Fin g → (𝓞 E →+* K)), ∀ a j, r a (b j) = ty j a • b j := by
  classical
  have hc : ∀ a c : 𝓞 E, Commute (r a) (r c) := fun a c => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ (a c : 𝓞 E) (z : K),
      Set.MapsTo (r a) ((r c).maxGenEigenspace z) ((r c).maxGenEigenspace z) :=
    fun a c z => Module.End.mapsTo_maxGenEigenspace_of_comm (hc c a) z
  let W : (𝓞 E → K) → Submodule K V := fun χ => ⨅ a, (r a).maxGenEigenspace (χ a)
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a => r a) hmaps)
      (Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun a => r a) hmaps
        fun a => Module.End.iSup_maxGenEigenspace_eq_top (r a))
  let B := hint.collectedBasis fun χ => Module.finBasis K (W χ)
  have : Finite (Σ χ, Fin (Module.finrank K (W χ))) := Module.Finite.finite_basis B
  let _ : Fintype (Σ χ, Fin (Module.finrank K (W χ))) := Fintype.ofFinite _
  have heig : ∀ s : (Σ χ, Fin (Module.finrank K (W χ))), ∀ a, r a (B s) = s.1 a • B s := by
    intro s a
    have hm : B s ∈ W s.1 := hint.collectedBasis_mem _ s
    have hm' : B s ∈ (r a).maxGenEigenspace (s.1 a) := (Submodule.mem_iInf _).1 hm a
    rw [(isSemisimple_ringOfIntegers_action r a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hm'
    exact Module.End.mem_eigenspace_iff.1 hm'
  choose t ht using fun s : (Σ χ, Fin (Module.finrank K (W χ))) =>
    exists_ringHom_eq_eigenvalue r (B.ne_zero s) s.1 (heig s)
  let e := Fintype.equivFin (Σ χ, Fin (Module.finrank K (W χ)))
  refine ⟨Fintype.card _, B.reindex e, fun j => t (e.symm j), fun a j => ?_⟩
  rw [Module.Basis.reindex_apply, ht, heig]
end GlobalTheory.AdaptedBasis
