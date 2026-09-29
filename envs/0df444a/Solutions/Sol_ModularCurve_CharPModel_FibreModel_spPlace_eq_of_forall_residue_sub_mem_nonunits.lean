-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/349733bd-11ca-5f49-a91e-7034ec92022e

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_separable_phi_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve.CharPModel AlgebraicCurve AlgebraicCurve.Place IsLocalRing Polynomial IntermediateField"
open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC jqModC_rat map_jqModC modularFunctionFieldC jqModC_mem jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffEmb laurentBaseChange CharPModel.jBar CharPModel.FibreModel modularFunctionFieldBar coeffMap_jqModC coeffMap_jqNModC isCurveOver_modularFunctionFieldBar finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC transcendental_jqModC transcendental_coeffEmb_jq isSeparable_jqNModC_of_separable_phi_map"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "FibreModel.piFin_mem_spPlace_nonunits_iff jBar jNBar constantsHom affineBaseFin FibreModel"
namespace W3G1
p2m_open "ModularCurve.CharPModel ModularCurve"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {j : F}

private theorem isPrincipalIdealRing_adjoin_singleton' (hj : Transcendental K j) :
    IsPrincipalIdealRing (Algebra.adjoin K ({j} : Set F)) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K j hj).toRingHom
    (Polynomial.algEquivOfTranscendental K j hj).surjective

private theorem isDedekindDomain_adjoin_singleton' (hj : Transcendental K j) :
    IsDedekindDomain (Algebra.adjoin K ({j} : Set F)) :=
  haveI := isPrincipalIdealRing_adjoin_singleton' hj
  inferInstance

private theorem isDedekindDomain_integralClosure_adjoin' (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F] :
    IsDedekindDomain (integralClosure (Algebra.adjoin K ({j} : Set F)) F) :=
  haveI := isDedekindDomain_adjoin_singleton' hj
  integralClosure.isDedekindDomain (Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

private theorem isFractionRing_integralClosure_adjoin' (hj : Transcendental K j) [FiniteDimensional K⟮j⟯ F] :
    IsFractionRing (integralClosure (Algebra.adjoin K ({j} : Set F)) F) F :=
  haveI := isDedekindDomain_adjoin_singleton' hj
  integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

private theorem integralClosure_adjoin_le_valuationSubring' (O : ValuationSubring F)
    (hK : ∀ c : K, algebraMap K F c ∈ O) (hjO : j ∈ O)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) : (r : F) ∈ O := by
  let O' : Subalgebra K F :=
    { O.toSubring with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ O' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjO)
  let φ : Algebra.adjoin K ({j} : Set F) →+* O :=
    (Subalgebra.val _).toRingHom.codRestrict O.toSubring (fun y => hle y.2)
  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  have hint : IsIntegral O (r : F) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map]
    exact hpr
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem exists_monic_of_mem_integralClosure_adjoin (S : Subring F)
    (hK : ∀ c : K, algebraMap K F c ∈ S) (hjS : j ∈ S)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) :
    ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype (r : F) p = 0 := by
  let S' : Subalgebra K F :=
    { S with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ S' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjS)
  let φ : Algebra.adjoin K ({j} : Set F) →+* S :=
    (Subalgebra.val _).toRingHom.codRestrict S (fun y => hle y.2)
  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  refine ⟨p.map φ, hp.map φ, ?_⟩
  rw [eval₂_map]
  exact hpr

private theorem place_eq_of_forall_integral_mem_nonunits_iff (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F]
    (Q₁ Q₂ : Place K F) (hj₁ : j ∈ Q₁.toValuationSubring) (hj₂ : j ∈ Q₂.toValuationSubring)
    (h : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      (r : F) ∈ Q₁.toValuationSubring.nonunits ↔ (r : F) ∈ Q₂.toValuationSubring.nonunits) :
    Q₁ = Q₂ := by
  haveI := isDedekindDomain_integralClosure_adjoin' (F := F) hj
  haveI := isFractionRing_integralClosure_adjoin' (F := F) hj
  have hw₁ : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      algebraMap _ F r ∈ Q₁.toValuationSubring :=
    fun r => integralClosure_adjoin_le_valuationSubring' _ Q₁.algebraMap_mem' hj₁ r
  have hw₂ : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      algebraMap _ F r ∈ Q₂.toValuationSubring :=
    fun r => integralClosure_adjoin_le_valuationSubring' _ Q₂.algebraMap_mem' hj₂ r
  have hc : centerHeightOneSpectrum _ Q₁ hw₁ = centerHeightOneSpectrum _ Q₂ hw₂ := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [centerHeightOneSpectrum_asIdeal, centerHeightOneSpectrum_asIdeal]
    ext r
    rw [mem_center_iff, mem_center_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact h r
  apply Place.ext
  rw [toValuationSubring_eq_of_forall_mem Q₁ hw₁, toValuationSubring_eq_of_forall_mem Q₂ hw₂, hc]

end Generic

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime]
  [CharP (ResidueField ↥A) ℓ]

private def affineBaseFinIncl (S : Subring (modularFunctionFieldBar N))
    (hc : ∀ a : A, constantsHom N A a ∈ S) (hj : jBar N ∈ S) : affineBaseFin N A →+* S where
  toFun f := ⟨f, (Subring.closure_le.mpr (by
      rintro g (⟨a, rfl⟩ | hg)
      · exact hc a
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hj)) f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_affineBaseFinIncl (S : Subring (modularFunctionFieldBar N))
    (hc : ∀ a : A, constantsHom N A a ∈ S) (hj : jBar N ∈ S) (f : affineBaseFin N A) :
    ((affineBaseFinIncl S hc hj f : S) : modularFunctionFieldBar N) = f := rfl

private theorem isIntegral_of_integralFin (S : Subring (modularFunctionFieldBar N))
    (hc : ∀ a : A, constantsHom N A a ∈ S) (hj : jBar N ∈ S) {b : modularFunctionFieldBar N}
    (hb : ∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype b p = 0) :
    ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0 := by
  obtain ⟨p, hp, heval⟩ := hb
  refine ⟨p.map (affineBaseFinIncl S hc hj), hp.map _, ?_⟩
  rw [eval₂_map]
  have hcomp : S.subtype.comp (affineBaseFinIncl S hc hj) = (affineBaseFin N A).subtype :=
    RingHom.ext fun f => rfl
  rw [hcomp]
  exact heval

private theorem isIntegral_adjoin_jBar (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A)) (b : fm.BFin) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))
      (b : modularFunctionFieldBar N) := by
  have hc : ∀ a : A, constantsHom N A a ∈
      (Algebra.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))).toSubring :=
    fun a => Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
  have hj : jBar N ∈
      (Algebra.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))).toSubring :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  obtain ⟨p, hp, heval⟩ := isIntegral_of_integralFin _ hc hj (fm.integralFin b)
  exact ⟨p, hp, heval⟩

private theorem coeffMap_jqModC_eq_coe_jBar :
    coeffMap A.subtype (jqModC ↥A) = ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
  have h1 : coeffMap A.subtype (jqModC ↥A) = (jqModC ↥A).map (A.subtype : ↥A →+* AlgebraicClosure ℚ) := rfl
  have h2 : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
    rw [jqModC_rat]; rfl
  rw [h1, h2, map_jqModC, map_jqModC]

private theorem jBar_mem_integers
    (R : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField ↥A) N))
    (hspec : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField ↥A) N) :
            LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) y) :
    (jBar N : modularFunctionFieldBar N) ∈ R.integers := by
  have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar N := by
    rw [coeffMap_jqModC_eq_coe_jBar (N := N)]
    exact (jBar N).2
  obtain ⟨hint, -⟩ := hspec (jqModC ↥A) hy
  have he : (⟨coeffMap A.subtype (jqModC ↥A), hy⟩ : modularFunctionFieldBar N) = jBar N :=
    Subtype.ext (coeffMap_jqModC_eq_coe_jBar (N := N))
  rw [he] at hint
  exact hint

private theorem bfin_mem_integers (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (R : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField ↥A) N))
    (hspec : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField ↥A) N) :
            LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) y)
    (b : fm.BFin) : (b : modularFunctionFieldBar N) ∈ R.integers := by
  have hc : ∀ a : A, constantsHom N A a ∈ R.integers.toSubring :=
    fun a => (R.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2
  have hj : jBar N ∈ R.integers.toSubring := jBar_mem_integers R hspec
  obtain ⟨p, hp, heval⟩ := isIntegral_of_integralFin _ hc hj (fm.integralFin b)

  have hint : IsIntegral R.integers (b : modularFunctionFieldBar N) := ⟨p, hp, heval⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

private theorem coeffMap_jqNModC_eq_coe_jNBar :
    coeffMap A.subtype (jqNModC ↥A N) = ((jNBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [coeffMap_jqNModC]
  show jqNModC (AlgebraicClosure ℚ) N = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqNModC ℚ N)
  rw [coeffMap_jqNModC]

section Rho

variable (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
  (hred : Function.Surjective (residue ↥A))
  (R : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField ↥A) N))
  (hspec : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
    ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
      ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField ↥A) N) :
          LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) y)

private def residueBFin : fm.BFin →+* modularFunctionFieldC (ResidueField ↥A) N where
  toFun z := R.residue ⟨(z : modularFunctionFieldBar N), bfin_mem_integers fm R hspec z⟩
  map_one' := R.residue.map_one
  map_mul' z w := R.residue.map_mul ⟨(z : modularFunctionFieldBar N), bfin_mem_integers fm R hspec z⟩
    ⟨(w : modularFunctionFieldBar N), bfin_mem_integers fm R hspec w⟩
  map_zero' := R.residue.map_zero
  map_add' z w := R.residue.map_add ⟨(z : modularFunctionFieldBar N), bfin_mem_integers fm R hspec z⟩
    ⟨(w : modularFunctionFieldBar N), bfin_mem_integers fm R hspec w⟩

private theorem residueBFin_apply (z : fm.BFin) :
    residueBFin fm R hspec z = R.residue ⟨(z : modularFunctionFieldBar N), bfin_mem_integers fm R hspec z⟩ := rfl

include hred in

private theorem ker_piFin_le_ker_residueBFin : RingHom.ker fm.piFin ≤ RingHom.ker (residueBFin fm R hspec) := by
  have _ := hred
  rw [fm.ker_piFin, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, residueBFin_apply]
  have h1 := R.residue_algebraMap a
  have e : (⟨((⟨constantsHom N A a, fm.constFin_mem a⟩ : fm.BFin) : modularFunctionFieldBar N),
      bfin_mem_integers fm R hspec ⟨constantsHom N A a, fm.constFin_mem a⟩⟩ : R.integers) =
      ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ),
        (R.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ := rfl
  rw [e, h1, (residue_eq_zero_iff a).mpr ha, map_zero]

private theorem residueBFin_const (a : A) :
    residueBFin fm R hspec ⟨constantsHom N A a, fm.constFin_mem a⟩ = fm.piFin ⟨constantsHom N A a, fm.constFin_mem a⟩ := by
  rw [fm.piFin_const, residueBFin_apply]
  exact R.residue_algebraMap a

private theorem residueBFin_jBar :
    residueBFin fm R hspec ⟨jBar N, fm.jBar_mem⟩ = fm.piFin ⟨jBar N, fm.jBar_mem⟩ := by
  have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar N := by
    rw [coeffMap_jqModC_eq_coe_jBar (N := N)]
    exact (jBar N).2
  obtain ⟨hint, hres⟩ := hspec (jqModC ↥A) hy
  have e : (⟨((⟨jBar N, fm.jBar_mem⟩ : fm.BFin) : modularFunctionFieldBar N),
      bfin_mem_integers fm R hspec ⟨jBar N, fm.jBar_mem⟩⟩ : R.integers) =
      ⟨⟨coeffMap A.subtype (jqModC ↥A), hy⟩, hint⟩ :=
    Subtype.ext (Subtype.ext (coeffMap_jqModC_eq_coe_jBar (N := N)).symm)
  rw [fm.piFin_j, residueBFin_apply, e]
  apply Subtype.ext
  rw [hres, coeffMap_jqModC]

private theorem residueBFin_jNBar :
    residueBFin fm R hspec ⟨jNBar N, fm.jNBar_mem⟩ = fm.piFin ⟨jNBar N, fm.jNBar_mem⟩ := by
  have hy : coeffMap A.subtype (jqNModC ↥A N) ∈ modularFunctionFieldBar N := by
    rw [coeffMap_jqNModC_eq_coe_jNBar (N := N)]
    exact (jNBar N).2
  obtain ⟨hint, hres⟩ := hspec (jqNModC ↥A N) hy
  have e : (⟨((⟨jNBar N, fm.jNBar_mem⟩ : fm.BFin) : modularFunctionFieldBar N),
      bfin_mem_integers fm R hspec ⟨jNBar N, fm.jNBar_mem⟩⟩ : R.integers) =
      ⟨⟨coeffMap A.subtype (jqNModC ↥A N), hy⟩, hint⟩ :=
    Subtype.ext (Subtype.ext (coeffMap_jqNModC_eq_coe_jNBar (N := N)).symm)
  rw [fm.piFin_jN, residueBFin_apply, e]
  apply Subtype.ext
  rw [hres, coeffMap_jqNModC]

private def baseFinN (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) : Subring (modularFunctionFieldBar N) :=
  Subring.closure (Set.range (constantsHom N A) ∪ {jBar N, jNBar N})

private theorem baseFinN_le_bfin : baseFinN N A ≤ fm.BFin := by
  refine Subring.closure_le.mpr ?_
  rintro f (⟨a, rfl⟩ | hf)
  · exact fm.constFin_mem a
  · rcases hf with rfl | hf
    · exact fm.jBar_mem
    · rw [Set.mem_singleton_iff] at hf
      rw [hf]
      exact fm.jNBar_mem

private theorem residueBFin_eq_piFin_of_mem_baseFinN_aux {zv : modularFunctionFieldBar N} (hz : zv ∈ baseFinN N A) :
    ∃ hB : zv ∈ fm.BFin, residueBFin fm R hspec ⟨zv, hB⟩ = fm.piFin ⟨zv, hB⟩ := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | hx
      · exact ⟨fm.constFin_mem a, residueBFin_const fm R hspec a⟩
      · rcases hx with rfl | hx
        · exact ⟨fm.jBar_mem, residueBFin_jBar fm R hspec⟩
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨fm.jNBar_mem, residueBFin_jNBar fm R hspec⟩
  | zero => exact ⟨zero_mem _, by rw [show (⟨0, zero_mem _⟩ : fm.BFin) = 0 from rfl, map_zero, map_zero]⟩
  | one => exact ⟨one_mem _, by rw [show (⟨1, one_mem _⟩ : fm.BFin) = 1 from rfl, map_one, map_one]⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨hx, ex⟩ := ihx
      obtain ⟨hy, ey⟩ := ihy
      refine ⟨add_mem hx hy, ?_⟩
      rw [show (⟨x + y, add_mem hx hy⟩ : fm.BFin) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, map_add, ex, ey]
  | neg x _ ihx =>
      obtain ⟨hx, ex⟩ := ihx
      refine ⟨neg_mem hx, ?_⟩
      rw [show (⟨-x, neg_mem hx⟩ : fm.BFin) = -⟨x, hx⟩ from rfl, map_neg, map_neg, ex]
  | mul x y _ _ ihx ihy =>
      obtain ⟨hx, ex⟩ := ihx
      obtain ⟨hy, ey⟩ := ihy
      refine ⟨mul_mem hx hy, ?_⟩
      rw [show (⟨x * y, mul_mem hx hy⟩ : fm.BFin) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul, map_mul, ex, ey]

private theorem residueBFin_eq_piFin_of_mem_baseFinN (z : fm.BFin) (hz : (z : modularFunctionFieldBar N) ∈ baseFinN N A) :
    residueBFin fm R hspec z = fm.piFin z := by
  obtain ⟨hB, e⟩ := residueBFin_eq_piFin_of_mem_baseFinN_aux fm R hspec hz
  exact e

include hred in

private theorem exists_baseFinN_of_mem_adjoin {r : LaurentSeries (ResidueField ↥A)}
    (hr : r ∈ Algebra.adjoin (ResidueField ↥A)
      ({jqModC (ResidueField ↥A), jqNModC (ResidueField ↥A) N} : Set (LaurentSeries (ResidueField ↥A)))) :
    ∃ z : fm.BFin, (z : modularFunctionFieldBar N) ∈ baseFinN N A ∧
      ((fm.piFin z : modularFunctionFieldC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) = r := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨⟨jBar N, fm.jBar_mem⟩, Subring.subset_closure (Or.inr (Set.mem_insert _ _)), ?_⟩
        rw [fm.piFin_j]
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨⟨jNBar N, fm.jNBar_mem⟩,
          Subring.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
        rw [fm.piFin_jN]
  | algebraMap c =>
      obtain ⟨a, rfl⟩ := hred c
      refine ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, Subring.subset_closure (Or.inl ⟨a, rfl⟩), ?_⟩
      rw [fm.piFin_const]
      rfl
  | add x y _ _ ihx ihy =>
      obtain ⟨s, hs, es⟩ := ihx
      obtain ⟨t, ht, et⟩ := ihy
      refine ⟨s + t, add_mem hs ht, ?_⟩
      rw [map_add, ← es, ← et]
      rfl
  | mul x y _ _ ihx ihy =>
      obtain ⟨s, hs, es⟩ := ihx
      obtain ⟨t, ht, et⟩ := ihy
      refine ⟨s * t, mul_mem hs ht, ?_⟩
      rw [map_mul, ← es, ← et]
      rfl

include hred hspec in

private theorem residue_eq_piFin (b : fm.BFin) :
    ∃ hb : (b : modularFunctionFieldBar N) ∈ R.integers, R.residue ⟨b, hb⟩ = fm.piFin b := by
  refine ⟨bfin_mem_integers fm R hspec b, ?_⟩
  show residueBFin fm R hspec b = fm.piFin b
  have hmem : ((fm.piFin b : modularFunctionFieldC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) ∈
      IntermediateField.adjoin (ResidueField ↥A)
        ({jqModC (ResidueField ↥A), jqNModC (ResidueField ↥A) N} : Set (LaurentSeries (ResidueField ↥A))) :=
    (fm.piFin b).2
  obtain ⟨r, hr, s, hs, hdiv⟩ := IntermediateField.mem_adjoin_iff_div.mp hmem
  obtain ⟨br, hbr, er⟩ := exists_baseFinN_of_mem_adjoin fm hred hr
  obtain ⟨bs, hbs, es⟩ := exists_baseFinN_of_mem_adjoin fm hred hs
  by_cases hs0 : s = 0
  · have hπb : fm.piFin b = 0 := by
      apply Subtype.ext
      rw [hdiv, hs0, div_zero]
      rfl
    have hρb : residueBFin fm R hspec b = 0 := ker_piFin_le_ker_residueBFin fm hred R hspec hπb
    rw [hρb, hπb]
  · have hz : b * bs - br ∈ RingHom.ker fm.piFin := by
      rw [RingHom.mem_ker, map_sub, map_mul]
      apply Subtype.ext
      show ((fm.piFin b : modularFunctionFieldC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) *
          ((fm.piFin bs : modularFunctionFieldC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) -
          ((fm.piFin br : modularFunctionFieldC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) = 0
      rw [er, es, hdiv, div_mul_cancel₀ r hs0, sub_self]
    have hρz := ker_piFin_le_ker_residueBFin fm hred R hspec hz
    rw [RingHom.mem_ker, map_sub, map_mul, residueBFin_eq_piFin_of_mem_baseFinN fm R hspec bs hbs,
      residueBFin_eq_piFin_of_mem_baseFinN fm R hspec br hbr, sub_eq_zero] at hρz
    rw [RingHom.mem_ker, map_sub, map_mul, sub_eq_zero] at hz
    have hne : fm.piFin bs ≠ 0 := by
      intro h0
      apply hs0
      rw [← es, h0]
      rfl
    exact mul_right_cancel₀ hne (hρz.trans hz.symm)

end Rho

private theorem exists_sub_const_mem_nonunits (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a₀ : A)
    (ha₀ : 0 < P.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a₀ : AlgebraicClosure ℚ)))
    (b : fm.BFin) :
    ∃ a : A, (b : modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ∈
      P.toValuationSubring.nonunits := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N

  have hdeg : P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P
  haveI : Module.Finite (AlgebraicClosure ℚ) P.ResidueField :=
    Module.finite_of_finrank_eq_succ (n := 0)
      (hdeg : Module.finrank (AlgebraicClosure ℚ) P.ResidueField = 1)
  have hbij : Function.Bijective (algebraMap (AlgebraicClosure ℚ) P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ)
  let e : AlgebraicClosure ℚ ≃+* P.ResidueField := RingEquiv.ofBijective _ hbij
  let φ : P.toValuationSubring →+* AlgebraicClosure ℚ :=
    e.symm.toRingHom.comp (IsLocalRing.residue P.toValuationSubring)
  have hφ : ∀ f : P.toValuationSubring, e (φ f) = IsLocalRing.residue P.toValuationSubring f :=
    fun f => e.apply_symm_apply _
  have he : ∀ c : AlgebraicClosure ℚ, e c = IsLocalRing.residue P.toValuationSubring
      ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c, P.algebraMap_mem' c⟩ := fun c => rfl
  have hφc : ∀ c : AlgebraicClosure ℚ,
      φ ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c, P.algebraMap_mem' c⟩ = c := by
    intro c
    apply e.injective
    rw [hφ, he]

  have hφm : ∀ f : P.toValuationSubring, (f : modularFunctionFieldBar N) -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (φ f) ∈ P.toValuationSubring.nonunits := by
    intro f
    have hmem : (f : modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (φ f) ∈ P.toValuationSubring :=
      sub_mem f.2 (P.algebraMap_mem' _)
    have hk : (⟨_, hmem⟩ : P.toValuationSubring) ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      have e1 : (⟨_, hmem⟩ : P.toValuationSubring) =
          f - ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (φ f), P.algebraMap_mem' _⟩ := rfl
      rw [e1, map_sub, ← he, hφ, sub_self]
    exact ValuationSubring.coe_mem_nonunits_iff.mpr hk

  have hφ0 : ∀ f : P.toValuationSubring, f ∈ IsLocalRing.maximalIdeal P.toValuationSubring → φ f = 0 := by
    intro f hf
    apply e.injective
    rw [hφ, map_zero]
    exact (IsLocalRing.residue_eq_zero_iff f).mpr hf

  have hj0 : jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at ha₀
    exact lt_irrefl _ ha₀
  have hjm : jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ) ∈
      P.toValuationSubring := P.mem_of_ord_nonneg hj0 ha₀.le
  have hjO : jBar N ∈ P.toValuationSubring := by
    have h := add_mem hjm (P.algebraMap_mem' (a₀ : AlgebraicClosure ℚ))
    rwa [sub_add_cancel] at h
  have hφj : φ ⟨jBar N, hjO⟩ = (a₀ : AlgebraicClosure ℚ) := by
    have hsplit : (⟨jBar N, hjO⟩ : P.toValuationSubring) =
        ⟨_, hjm⟩ + ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ),
          P.algebraMap_mem' _⟩ := by
      apply Subtype.ext
      show jBar N = (jBar N - _) + _
      rw [sub_add_cancel]
    rw [hsplit, map_add, hφc, hφ0 _ ((P.mem_maximalIdeal_iff_ord_pos hj0 hjm).mpr ha₀), zero_add]

  have hc : ∀ a : A, constantsHom N A a ∈ P.toValuationSubring.toSubring :=
    fun a => P.algebraMap_mem' (a : AlgebraicClosure ℚ)
  have hjS : jBar N ∈ P.toValuationSubring.toSubring := hjO
  have hval : ∀ t : affineBaseFin N A,
      φ (affineBaseFinIncl P.toValuationSubring.toSubring hc hjS t) ∈ A := by
    rintro ⟨t, ht⟩
    suffices hmain : ∃ hO : t ∈ P.toValuationSubring, φ ⟨t, hO⟩ ∈ A by
      obtain ⟨hO, hA⟩ := hmain
      exact hA
    induction ht using Subring.closure_induction with
    | mem x hx =>
        rcases hx with ⟨a, rfl⟩ | hx
        · exact ⟨hc a, by rw [show (⟨constantsHom N A a, hc a⟩ : P.toValuationSubring) =
              ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ),
                P.algebraMap_mem' _⟩ from rfl, hφc]; exact a.2⟩
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨hjO, by rw [hφj]; exact a₀.2⟩
    | zero => exact ⟨zero_mem _, by rw [show (⟨0, zero_mem _⟩ : P.toValuationSubring) = 0 from rfl, map_zero]; exact zero_mem _⟩
    | one => exact ⟨one_mem _, by rw [show (⟨1, one_mem _⟩ : P.toValuationSubring) = 1 from rfl, map_one]; exact one_mem _⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨hx, ex⟩ := ihx
        obtain ⟨hy, ey⟩ := ihy
        refine ⟨add_mem hx hy, ?_⟩
        rw [show (⟨x + y, add_mem hx hy⟩ : P.toValuationSubring) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]
        exact add_mem ex ey
    | neg x _ ihx =>
        obtain ⟨hx, ex⟩ := ihx
        refine ⟨neg_mem hx, ?_⟩
        rw [show (⟨-x, neg_mem hx⟩ : P.toValuationSubring) = -⟨x, hx⟩ from rfl, map_neg]
        exact neg_mem ex
    | mul x y _ _ ihx ihy =>
        obtain ⟨hx, ex⟩ := ihx
        obtain ⟨hy, ey⟩ := ihy
        refine ⟨mul_mem hx hy, ?_⟩
        rw [show (⟨x * y, mul_mem hx hy⟩ : P.toValuationSubring) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
        exact mul_mem ex ey

  obtain ⟨p, hp, heval⟩ := fm.integralFin b
  have hp' : (p.map (affineBaseFinIncl P.toValuationSubring.toSubring hc hjS)).Monic := hp.map _
  have heval' : Polynomial.eval₂ P.toValuationSubring.toSubring.subtype (b : modularFunctionFieldBar N)
      (p.map (affineBaseFinIncl P.toValuationSubring.toSubring hc hjS)) = 0 := by
    rw [eval₂_map]
    have hcomp : P.toValuationSubring.toSubring.subtype.comp
        (affineBaseFinIncl P.toValuationSubring.toSubring hc hjS) = (affineBaseFin N A).subtype :=
      RingHom.ext fun f => rfl
    rw [hcomp]
    exact heval
  have hbO : (b : modularFunctionFieldBar N) ∈ P.toValuationSubring := by
    have hint : IsIntegral P.toValuationSubring (b : modularFunctionFieldBar N) := ⟨_, hp', heval'⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    rw [← hy]
    exact y.2

  have hevalO : Polynomial.eval (⟨(b : modularFunctionFieldBar N), hbO⟩ : P.toValuationSubring)
      (p.map (affineBaseFinIncl P.toValuationSubring.toSubring hc hjS)) = 0 := by
    apply Subtype.val_injective
    have h := Polynomial.eval₂_hom P.toValuationSubring.toSubring.subtype
      (p := p.map (affineBaseFinIncl P.toValuationSubring.toSubring hc hjS))
      (⟨(b : modularFunctionFieldBar N), hbO⟩ : P.toValuationSubring.toSubring)

    exact h.symm.trans heval'

  set r : Polynomial (AlgebraicClosure ℚ) :=
    (p.map (affineBaseFinIncl P.toValuationSubring.toSubring hc hjS)).map φ with hr
  have hrm : r.Monic := hp'.map φ
  have hroot : r.eval (φ ⟨(b : modularFunctionFieldBar N), hbO⟩) = 0 := by
    rw [hr, eval_map, eval₂_hom, hevalO, map_zero]
  have hlifts : r ∈ Polynomial.lifts (algebraMap (↥A) (AlgebraicClosure ℚ)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hr, coeff_map, coeff_map]
    exact ⟨⟨_, hval (p.coeff n)⟩, rfl⟩
  obtain ⟨q, hqr, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlifts hrm
  have hint : IsIntegral (↥A) (φ ⟨(b : modularFunctionFieldBar N), hbO⟩) := by
    refine ⟨q, hqm, ?_⟩
    rw [eval₂_eq_eval_map, hqr]
    exact hroot
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨a, ?_⟩
  have hm := hφm ⟨(b : modularFunctionFieldBar N), hbO⟩
  rw [← ha] at hm
  exact hm

private theorem exists_piFin_eq_of_mem_integralClosure (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (hred : Function.Surjective (residue ↥A))
    (r : integralClosure (Algebra.adjoin (ResidueField ↥A)
      ({(⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ : modularFunctionFieldC (ResidueField ↥A) N)} :
        Set (modularFunctionFieldC (ResidueField ↥A) N))) (modularFunctionFieldC (ResidueField ↥A) N)) :
    ∃ b : fm.BFin, fm.piFin b = (r : modularFunctionFieldC (ResidueField ↥A) N) := by
  have hK : ∀ c : ResidueField ↥A,
      algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) c ∈ fm.piFin.range := by
    intro c
    obtain ⟨a, rfl⟩ := hred c
    exact ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, fm.piFin_const a⟩
  have hjS : (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
      modularFunctionFieldC (ResidueField ↥A) N) ∈ fm.piFin.range :=
    ⟨⟨jBar N, fm.jBar_mem⟩, fm.piFin_j⟩
  obtain ⟨p, hp, heval⟩ := exists_monic_of_mem_integralClosure_adjoin fm.piFin.range hK hjS r
  obtain ⟨b, hb⟩ := fm.intClosed_piFin _ ⟨p, hp, heval⟩
  exact ⟨b, hb⟩

private theorem place_eq_of_forall_piFin_mem_nonunits_iff' (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (hred : Function.Surjective (residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsepE : IsSeparable (IntermediateField.adjoin (ResidueField ↥A) ({jqModC (ResidueField ↥A)} :
        Set (LaurentSeries (ResidueField ↥A)))) (jqNModC (ResidueField ↥A) N))
    (Q₁ Q₂ : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hj₁ : (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
        modularFunctionFieldC (ResidueField ↥A) N) ∈ Q₁.toValuationSubring)
    (hj₂ : (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
        modularFunctionFieldC (ResidueField ↥A) N) ∈ Q₂.toValuationSubring)
    (h : ∀ b : fm.BFin, fm.piFin b ∈ Q₁.toValuationSubring.nonunits ↔
      fm.piFin b ∈ Q₂.toValuationSubring.nonunits) :
    Q₁ = Q₂ := by
  obtain ⟨hFD, hSep⟩ := finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
    (ResidueField ↥A) N (dataAll N (dvd_refl N)) hsepE
  haveI := hFD
  haveI := hSep
  have hjt : Transcendental (ResidueField ↥A) ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
      modularFunctionFieldC (ResidueField ↥A) N)) := by
    have hinj : Function.Injective (algebraMap (modularFunctionFieldC (ResidueField ↥A) N)
        (LaurentSeries (ResidueField ↥A))) := Subtype.val_injective
    exact (transcendental_algebraMap_iff hinj).mp (transcendental_jqModC (ResidueField ↥A))
  refine place_eq_of_forall_integral_mem_nonunits_iff hjt Q₁ Q₂ hj₁ hj₂ (fun r => ?_)
  obtain ⟨b, hb⟩ := exists_piFin_eq_of_mem_integralClosure fm hred r
  rw [← hb]
  exact h b

private theorem place_eq_of_forall_piFin_mem_nonunits_iff (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (hred : Function.Surjective (residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (Q₁ Q₂ : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hj₁ : (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
        modularFunctionFieldC (ResidueField ↥A) N) ∈ Q₁.toValuationSubring)
    (hj₂ : (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
        modularFunctionFieldC (ResidueField ↥A) N) ∈ Q₂.toValuationSubring)
    (h : ∀ b : fm.BFin, fm.piFin b ∈ Q₁.toValuationSubring.nonunits ↔
      fm.piFin b ∈ Q₂.toValuationSubring.nonunits) :
    Q₁ = Q₂ :=
  place_eq_of_forall_piFin_mem_nonunits_iff' fm hred dataAll
    (isSeparable_jqNModC_of_separable_phi_map (ResidueField ↥A) N (dataAll N (dvd_refl N)) hsep) Q₁ Q₂ hj₁ hj₂ h

private theorem jBar_sub_algebraMap_ne_zero (a₀ : A) :
    jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a₀ : AlgebraicClosure ℚ) ≠ 0 := by
  refine sub_ne_zero.mpr fun heq => ?_
  have htr : Transcendental (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N) := by
    show Transcendental (AlgebraicClosure ℚ)
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, _⟩ : modularFunctionFieldBar N)
    exact transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  exact htr (heq ▸ isAlgebraic_algebraMap (a₀ : AlgebraicClosure ℚ))

private theorem ord_pos_of_sub_const_mem_nonunits (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a₀ : A)
    (h : jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ) ∈
      P.toValuationSubring.nonunits) :
    0 < P.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a₀ : AlgebraicClosure ℚ)) := by
  set x := jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
    (a₀ : AlgebraicClosure ℚ) with hx_def
  have hx0 : x ≠ 0 := jBar_sub_algebraMap_ne_zero a₀
  have hmem : x ∈ P.toValuationSubring :=
    (P.toValuationSubring.valuation_le_one_iff x).mp
      (le_of_lt ((P.toValuationSubring.mem_nonunits_iff).mp h))
  have hmax : (⟨x, hmem⟩ : P.toValuationSubring) ∈ maximalIdeal P.toValuationSubring :=
    ValuationSubring.coe_mem_nonunits_iff.mp h
  exact (P.mem_maximalIdeal_iff_ord_pos hx0 hmem).mp hmax

private theorem jqModC_mem_spPlace (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (hred : Function.Surjective (residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a₀ : A)
    (ha₀ : 0 < P.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a₀ : AlgebraicClosure ℚ))) :
    (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
        modularFunctionFieldC (ResidueField ↥A) N) ∈
      (fm.spPlace hred dataAll hsep P).toValuationSubring := by
  set Q := fm.spPlace hred dataAll hsep P with hQdef

  have hmem_b : (jBar N - constantsHom N A a₀) ∈ fm.BFin :=
    sub_mem fm.jBar_mem (fm.constFin_mem a₀)
  set b : fm.BFin := ⟨jBar N - constantsHom N A a₀, hmem_b⟩ with hb_def

  have hconst : constantsHom N A a₀
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ) :=
    rfl

  have hrhs : ∃ a : A, a ∈ maximalIdeal A ∧
      ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) -
          algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ))
        ∈ P.toValuationSubring.nonunits := by
    refine ⟨0, zero_mem _, ?_⟩
    simp only [ZeroMemClass.coe_zero, map_zero, sub_zero]
    show (jBar N - constantsHom N A a₀) ∈ P.toValuationSubring.nonunits
    rw [hconst]
    have hx0 : (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (a₀ : AlgebraicClosure ℚ)) ≠ 0 := jBar_sub_algebraMap_ne_zero a₀
    have hmem : (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (a₀ : AlgebraicClosure ℚ)) ∈ P.toValuationSubring :=
      P.mem_of_ord_nonneg hx0 (le_of_lt ha₀)
    exact ValuationSubring.coe_mem_nonunits_iff.mpr
      ((P.mem_maximalIdeal_iff_ord_pos hx0 hmem).mpr ha₀)

  have hlhs : (fm.piFin b : modularFunctionFieldC (ResidueField ↥A) N) ∈ Q.toValuationSubring.nonunits :=
    (FibreModel.piFin_mem_spPlace_nonunits_iff fm hred dataAll hsep P a₀ ha₀ b).mpr hrhs

  have hpi : fm.piFin b = (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
      modularFunctionFieldC (ResidueField ↥A) N)
        - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)
          (residue ↥A a₀) := by
    have : b = (⟨jBar N, fm.jBar_mem⟩ : fm.BFin)
        - ⟨constantsHom N A a₀, fm.constFin_mem a₀⟩ := rfl
    rw [this, map_sub, fm.piFin_j, fm.piFin_const]
  rw [hpi] at hlhs

  have h1 : ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
      modularFunctionFieldC (ResidueField ↥A) N)
        - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)
          (residue ↥A a₀)) ∈ Q.toValuationSubring :=
    (Q.toValuationSubring.valuation_le_one_iff _).mp
      (le_of_lt ((Q.toValuationSubring.mem_nonunits_iff).mp hlhs))
  have h2 : algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)
      (residue ↥A a₀) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' (residue ↥A a₀)
  have := add_mem h1 h2
  simpa using this

private theorem algebraMap_residue_mem_nonunits_iff
    (Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)) (a : A) :
    algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) (residue ↥A a) ∈
        Q.toValuationSubring.nonunits ↔ a ∈ maximalIdeal ↥A := by
  constructor
  · intro h
    by_contra hna
    have hc : residue ↥A a ≠ 0 := fun h0 => hna ((residue_eq_zero_iff a).mp h0)
    set c : ResidueField ↥A := residue ↥A a with hcdef
    have hu : IsUnit (⟨algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) c,
        Q.algebraMap_mem' c⟩ : Q.toValuationSubring) := by
      refine IsUnit.of_mul_eq_one ⟨algebraMap (ResidueField ↥A) _ c⁻¹, Q.algebraMap_mem' c⁻¹⟩ ?_
      apply Subtype.ext
      show algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) c *
          algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    have hm : (⟨algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) c,
        Q.algebraMap_mem' c⟩ : Q.toValuationSubring) ∈ maximalIdeal Q.toValuationSubring :=
      ValuationSubring.coe_mem_nonunits_iff.mp h
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
  · intro h
    rw [(residue_eq_zero_iff a).mpr h, map_zero]
    exact zero_mem _

private theorem spPlace_eq_of_forall_residue_sub_mem_nonunits
    (fm : FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (hred : Function.Surjective (residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (R : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField ↥A) N))
    (hspec : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField ↥A) N) :
            LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) y)
    (x : R.integers) (hx : (x : modularFunctionFieldBar N) = jBar N)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hP : ∃ a : A, (x : modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits)
    (Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hQ : R.residue x ∈ Q.toValuationSubring)
    (hclause : ∀ h : R.integers,
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) {(x : modularFunctionFieldBar N)})
          (h : modularFunctionFieldBar N) →
        ∀ a : A, (h : modularFunctionFieldBar N) -
            algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)
              (residue ↥A a) ∈ Q.toValuationSubring.nonunits) :
    fm.spPlace hred dataAll hsep P = Q := by
  obtain ⟨xv, hxO⟩ := x
  change xv = jBar N at hx
  subst hx
  obtain ⟨a₀, ha₀'⟩ := hP
  have ha₀ := ord_pos_of_sub_const_mem_nonunits P a₀ ha₀'

  have hj₁ := jqModC_mem_spPlace fm hred dataAll hsep P a₀ ha₀
  obtain ⟨hbj, hresj⟩ := residue_eq_piFin fm hred R hspec ⟨jBar N, fm.jBar_mem⟩
  have hj₂ : (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ :
      modularFunctionFieldC (ResidueField ↥A) N) ∈ Q.toValuationSubring := by
    rw [← fm.piFin_j, ← hresj]
    exact hQ
  refine place_eq_of_forall_piFin_mem_nonunits_iff fm hred dataAll hsep _ Q hj₁ hj₂ (fun b => ?_)
  obtain ⟨hb, hres⟩ := residue_eq_piFin fm hred R hspec b
  have hint := isIntegral_adjoin_jBar fm b
  constructor
  · intro h1
    obtain ⟨a, ha𝔪, hba⟩ := (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep P a₀ ha₀ b).mp h1
    have hc := hclause ⟨b, hb⟩ hint a hba
    rw [hres, (residue_eq_zero_iff a).mpr ha𝔪, map_zero, sub_zero] at hc
    exact hc
  · intro h2
    obtain ⟨a, hba⟩ := exists_sub_const_mem_nonunits fm P a₀ ha₀ b
    have hc := hclause ⟨b, hb⟩ hint a hba
    rw [hres] at hc
    have hā : algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) (residue ↥A a) ∈
        Q.toValuationSubring.nonunits := by
      have hs := sub_mem h2 hc
      rwa [sub_sub_cancel] at hs
    have ha𝔪 : a ∈ maximalIdeal ↥A := (algebraMap_residue_mem_nonunits_iff Q a).mp hā
    exact (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep P a₀ ha₀ b).mpr ⟨a, ha𝔪, hba⟩

end ModularCurve.CharPModel.W3G1
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve.CharPModel.W3G1"
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve.CharPModel"
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve"

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))).Separable)
    (R : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar N)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A) (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N),
      ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ModularCurve.modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) = ModularCurve.coeffMap (IsLocalRing.residue A) y)
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N))
    (hP : ∃ a : A, ModularCurve.CharPModel.jBar N -
        algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits)
    (Q : AlgebraicCurve.Place (IsLocalRing.ResidueField A)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))
    (hclause : ∀ h : R.integers,
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          ({ModularCurve.CharPModel.jBar N} : Set (ModularCurve.modularFunctionFieldBar N)))
        (h : ModularCurve.modularFunctionFieldBar N) →
      ∀ a : A, (h : ModularCurve.modularFunctionFieldBar N) -
          algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits →
        R.residue h - algebraMap (IsLocalRing.ResidueField A)
            (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) (IsLocalRing.residue A a) ∈
          Q.toValuationSubring.nonunits) :
    fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P = Q := by
  let x : R.integers := ⟨ModularCurve.CharPModel.jBar N, ModularCurve.CharPModel.W3G1.jBar_mem_integers R hspec⟩
  have hx : (x : ModularCurve.modularFunctionFieldBar N) = ModularCurve.CharPModel.jBar N := rfl
  obtain ⟨a₀, ha₀⟩ := hP

  have hxi : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      ({ModularCurve.CharPModel.jBar N} : Set (ModularCurve.modularFunctionFieldBar N)))
      (x : ModularCurve.modularFunctionFieldBar N) :=
    isIntegral_algebraMap (R := Algebra.adjoin (AlgebraicClosure ℚ)
      ({ModularCurve.CharPModel.jBar N} : Set (ModularCurve.modularFunctionFieldBar N)))
      (x := ⟨ModularCurve.CharPModel.jBar N, Algebra.subset_adjoin (Set.mem_singleton _)⟩)
  have hQ : R.residue x ∈ Q.toValuationSubring := by
    have h1 : R.residue x - algebraMap (IsLocalRing.ResidueField A)
        (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) (IsLocalRing.residue A a₀) ∈
          Q.toValuationSubring :=
      Q.toValuationSubring.nonunits_subset (hclause x hxi a₀ ha₀)
    have h2 := add_mem h1 (Q.algebraMap_mem' (IsLocalRing.residue A a₀))
    rwa [sub_add_cancel] at h2
  exact ModularCurve.CharPModel.W3G1.spPlace_eq_of_forall_residue_sub_mem_nonunits fm Ideal.Quotient.mk_surjective
    dataAll hsep R hspec x hx P ⟨a₀, ha₀⟩ Q hQ hclause

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.ModularCurve.CharPModel.W3G1"

end S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits (solution)
