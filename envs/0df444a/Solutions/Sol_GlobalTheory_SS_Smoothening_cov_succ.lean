-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.cov_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:23.381279+00:00
-- url     : https://prove2.me/submissions/e603f0a5-316f-4caa-8c3b-5810191b34d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp
import Theorems.Thm_GlobalTheory_SS_Smoothening_genOpen_away
import Theorems.Thm_GlobalTheory_SS_Smoothening_genOpen_of_inj
import Theorems.Thm_GlobalTheory_SS_Smoothening_smooth_away_away
import Theorems.Thm_GlobalTheory_SS_Smoothening_smooth_away_of_inj
import Theorems.Thm_GlobalTheory_SS_Smoothening_defect_away
import Theorems.Thm_GlobalTheory_SS_Smoothening_free_of_away
import Theorems.Thm_GlobalTheory_SS_Smoothening_Cov_trans
import Theorems.Thm_GlobalTheory_SS_Smoothening_not_dvd_of_unit
import Theorems.Thm_GlobalTheory_SS_Smoothening_exists_lift
import Theorems.Thm_GlobalTheory_SS_Smoothening_cov_of_generic
import Theorems.Thm_GlobalTheory_SS_Smoothening_vanish_away
import Theorems.Thm_GlobalTheory_SS_Smoothening_vanish_isRadical
import Theorems.Thm_GlobalTheory_SS_Dil_exists_lift
import Theorems.Thm_GlobalTheory_T_unramified_ideal_locus_characterization
import Theorems.Thm_P2M_GlobalTheory_T_exists_smooth_free_away__350d1efab22d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R : Type} (K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {π : R} (hπ : Irreducible π)
include hπ
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution (hk : PerfectField (IsLocalRing.ResidueField R)) (c : ℕ)
    (ih : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B],
      Algebra.Smooth R (Localization.Away (algebraMap R B π)) → Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π c : Pts R B))
    (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B]
    (hB : Algebra.Smooth R (Localization.Away (algebraMap R B π))) :
    Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π (c + 1) : Pts R B) := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  refine cov_of_generic π _ (fun R' _ _ a h => h.1) ?_
  rintro E hE ⟨R₀, _, _, a₀, ha₀⟩
  have hU : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R' :=
    fun R' _ _ a ha => (hE R' a ha).1
  let I := vanish π E
  let k := IsLocalRing.ResidueField R
  have hI : I ≠ ⊤ := fun h => not_dvd_of_unit (hU R₀ a₀ ha₀) (isUnit_one.map a₀)
    ((h ▸ Submodule.mem_top : (1 : B) ∈ I) R₀ a₀ ha₀)
  haveI : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : IsReduced (B ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).1 (vanish_isRadical π E hU)
  have hm : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (B ⧸ I) r = 0 := by
    intro r hr
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
    rw [IsScalarTower.algebraMap_apply R B, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    intro R' _ _ a _
    rw [a.commutes]
    exact map_dvd _ hr
  letI : Algebra k (B ⧸ I) := (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R (B ⧸ I)) hm).toAlgebra
  haveI : IsScalarTower R k (B ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType k (B ⧸ I) := Algebra.FiniteType.of_restrictScalars_finiteType R k _
  obtain ⟨g, hg, hs, hfree⟩ := GlobalTheory.T.exists_smooth_free_away' k (B ⧸ I) ((B ⧸ I) ⊗[B] KaehlerDifferential R B)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  refine ⟨f, fun h => hg (Ideal.Quotient.eq_zero_iff_mem.2 h), ?_⟩
  let L := Localization.Away f
  let J : Ideal L := I.map (algebraMap B L)
  let jf := IsScalarTower.toAlgHom R B L
  haveI : IsLocalization.Away (Ideal.Quotient.mk I f) (L ⧸ J) := by
    have : IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers f)) (L ⧸ J) := inferInstance
    rwa [Algebra.algebraMapSubmonoid_powers] at this
  letI : Algebra k (L ⧸ J) := ((algebraMap (B ⧸ I) (L ⧸ J)).comp (algebraMap k (B ⧸ I))).toAlgebra
  haveI : IsScalarTower k (B ⧸ I) (L ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R k (L ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hs' : Algebra.Smooth k (L ⧸ J) := Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I f)) (Localization.Away (Ideal.Quotient.mk I f))
      (L ⧸ J)).restrictScalars k)
  have hfree' : Module.Free (L ⧸ J) ((L ⧸ J) ⊗[L] KaehlerDifferential R L) := by
    haveI := free_of_away (Ideal.Quotient.mk I f) _ (L ⧸ J) hfree
    haveI : Module.Free (L ⧸ J) ((L ⧸ J) ⊗[B] KaehlerDifferential R B) :=
      Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ I) (L ⧸ J) (L ⧸ J) _)
    exact Module.Free.of_equiv (kaehlerAway R f (L ⧸ J)).symm
  haveI : Algebra.FiniteType R L := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  haveI : Module.Flat R L := Module.Flat.trans R B L
  obtain ⟨B', _, _, φ, _, _, hi, hsurj, hpt⟩ := GlobalTheory.T.unramified_ideal_locus_characterization R π hπ L (fun R' _ _ a => E R' (a.comp jf))
    (fun R' _ _ a ha => hU R' _ ha) J (vanish_away π E hU f) k IsLocalRing.residue_surjective hs' hfree'
  refine Cov.trans (φ.comp jf) ((genOpen_away f).comp (genOpen_of_inj hπ.ne_zero φ hi hsurj))
    (ih B' (smooth_away_of_inj (smooth_away_away hB f) φ hi hsurj)) ?_
  rintro R' _ _ a ⟨ha, hu⟩
  obtain ⟨a', rfl⟩ := exists_lift f a hu
  obtain ⟨a'', rfl, hd⟩ := hpt R' a' c ha (defect_away f a' π _ (hE R' _ ha).2)
  exact ⟨a'', rfl, hU R' _ ha, hd⟩
end GlobalTheory.SS.Smoothening
