-- Prove2me | solution 1 for ModularCurve.FullLevel.existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/60caa78e-df40-5e9e-bdf3-d38accb82b0b

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

namespace RamZeroQ2

p2m_open "AlgebraicCurve ModularCurve~coeffMap_qExpand"

section Generic

variable {K F : Type*} [Field K] [Field F]

theorem pow_mem_iff (O : ValuationSubring F) (x : F) {n : ℕ} (hn : n ≠ 0) : x ^ n ∈ O ↔ x ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

variable [Algebra K F]

def transport (e : F ≃+* F) (he : ∀ c : K, ∃ c' : K, e.symm (algebraMap K F c) = algebraMap K F c')
    (v : Place K F) : Place K F where
  toValuationSubring := v.toValuationSubring.comap e.symm.toRingHom
  algebraMap_mem' c := by
    obtain ⟨c', hc'⟩ := he c
    rw [ValuationSubring.mem_comap]
    show e.symm (algebraMap K F c) ∈ v.toValuationSubring
    rw [hc']
    exact v.algebraMap_mem' c'
  ne_top' h := v.ne_top' <| by
    refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
    have hx : e x ∈ v.toValuationSubring.comap e.symm.toRingHom := by
      rw [h]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap] at hx
    have : e.symm.toRingHom (e x) = x := e.symm_apply_apply x
    rwa [this] at hx
  isPrincipalIdealRing' := by
    haveI : IsPrincipalIdealRing v.toValuationSubring := v.isPrincipalIdealRing'
    let f : v.toValuationSubring →+* (v.toValuationSubring.comap e.symm.toRingHom) :=
      { toFun := fun x => ⟨e x, by
          rw [ValuationSubring.mem_comap]
          have : e.symm.toRingHom (e (x : F)) = x := e.symm_apply_apply (x : F)
          rw [this]; exact x.2⟩
        map_one' := Subtype.ext (map_one e)
        map_mul' := fun x y => Subtype.ext (map_mul e _ _)
        map_zero' := Subtype.ext (map_zero e)
        map_add' := fun x y => Subtype.ext (map_add e _ _) }
    refine IsPrincipalIdealRing.of_surjective f ?_
    rintro ⟨y, hy⟩
    rw [ValuationSubring.mem_comap] at hy
    exact ⟨⟨e.symm y, hy⟩, Subtype.ext (e.apply_symm_apply y)⟩

theorem mem_transport_iff (e : F ≃+* F) (he : ∀ c : K, ∃ c' : K, e.symm (algebraMap K F c) = algebraMap K F c')
    (v : Place K F) (x : F) :
    x ∈ (transport e he v).toValuationSubring ↔ e.symm x ∈ v.toValuationSubring :=
  Iff.rfl

end Generic

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qExpand (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases h : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd (hk := h), qExpand_coeff_of_not_dvd (hk := h), map_zero]

noncomputable def coeffEquiv (φ : R ≃+* R) : LaurentSeries R ≃+* LaurentSeries R where
  toFun := coeffMap φ.toRingHom
  invFun := coeffMap φ.symm.toRingHom
  left_inv x := by
    show coeffMap φ.symm.toRingHom (coeffMap φ.toRingHom x) = x
    rw [coeffMap_coeffMap]
    have : φ.symm.toRingHom.comp φ.toRingHom = RingHom.id R := RingHom.ext fun a => φ.symm_apply_apply a
    rw [coeffMap_congr this, coeffMap_id]
  right_inv x := by
    show coeffMap φ.toRingHom (coeffMap φ.symm.toRingHom x) = x
    rw [coeffMap_coeffMap]
    have : φ.toRingHom.comp φ.symm.toRingHom = RingHom.id R := RingHom.ext fun a => φ.apply_symm_apply a
    rw [coeffMap_congr this, coeffMap_id]
  map_mul' x y := map_mul _ _ _
  map_add' x y := map_add _ _ _

theorem coeffEquiv_apply (φ : R ≃+* R) (x : LaurentSeries R) : coeffEquiv φ x = coeffMap φ.toRingHom x := rfl

theorem coeffEquiv_symm_apply (φ : R ≃+* R) (x : LaurentSeries R) :
    (coeffEquiv φ).symm x = coeffMap φ.symm.toRingHom x := rfl

variable (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]

theorem pow_eq_coeffMap_frobenius_qExpand (x : LaurentSeries κ) :
    x ^ p = coeffMap (frobenius κ p) (qExpand κ p x) :=
  ModularCurve.pow_char_eq_map_frobenius_qExpand p x

theorem pow_mul_eq_coeffMap_qExpand (x : LaurentSeries κ) :
    x ^ (p * p) = coeffMap ((frobenius κ p).comp (frobenius κ p)) (qExpand κ (p * p) x) := by
  rw [pow_mul, pow_eq_coeffMap_frobenius_qExpand κ p x, ← map_pow, pow_eq_coeffMap_frobenius_qExpand κ p,
    coeffMap_coeffMap, qExpand_qExpand]

variable [PerfectRing κ p]

noncomputable def φpp : κ ≃+* κ :=
  haveI : ExpChar κ p := ExpChar.prime Fact.out
  (frobeniusEquiv κ p).trans (frobeniusEquiv κ p)

theorem φpp_toRingHom :
    (φpp κ p).toRingHom = (frobenius κ p).comp (frobenius κ p) := by
  haveI : ExpChar κ p := ExpChar.prime Fact.out
  ext a
  rfl

noncomputable def θ : LaurentSeries κ ≃+* LaurentSeries κ := (coeffEquiv (φpp κ p)).symm

theorem θ_symm_apply (x : LaurentSeries κ) : (θ κ p).symm x = coeffMap (φpp κ p).toRingHom x := rfl

theorem qExpand_eq_θ_pow (x : LaurentSeries κ) : qExpand κ (p * p) x = ((θ κ p) x) ^ (p * p) := by
  have h := pow_mul_eq_coeffMap_qExpand κ p ((θ κ p) x)
  rw [← φpp_toRingHom, coeffMap_qExpand] at h
  have h2 : coeffMap (φpp κ p).toRingHom ((θ κ p) x) = x := by
    rw [← θ_symm_apply, RingEquiv.symm_apply_apply]
  rw [h2] at h
  exact h.symm

theorem pow_eq_qExpand_θ_symm (x : LaurentSeries κ) : x ^ (p * p) = qExpand κ (p * p) ((θ κ p).symm x) := by
  rw [qExpand_eq_θ_pow, RingEquiv.apply_symm_apply]

theorem θ_symm_algebraMap (c : κ) :
    (θ κ p).symm (algebraMap κ (LaurentSeries κ) c) = algebraMap κ (LaurentSeries κ) (φpp κ p c) := by
  rw [θ_symm_apply, coeffMap_algebraMap]; rfl

theorem θ_algebraMap (c : κ) :
    (θ κ p) (algebraMap κ (LaurentSeries κ) c) = algebraMap κ (LaurentSeries κ) ((φpp κ p).symm c) := by
  apply (θ κ p).symm.injective
  rw [RingEquiv.symm_apply_apply, θ_symm_algebraMap, RingEquiv.apply_symm_apply]

theorem θ_jqModC : (θ κ p) (jqModC κ) = jqModC κ := by
  apply (θ κ p).symm.injective
  rw [RingEquiv.symm_apply_apply, θ_symm_apply, jqModC_eq_map_intCast κ]
  show coeffMap (Int.castRingHom κ) (jqModC ℤ) = coeffMap (φpp κ p).toRingHom (coeffMap (Int.castRingHom κ) (jqModC ℤ))
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) _

theorem θ_jqNModC (N : ℕ) [NeZero N] : (θ κ p) (jqNModC κ N) = jqNModC κ N := by
  apply (θ κ p).symm.injective
  rw [RingEquiv.symm_apply_apply, θ_symm_apply]
  show qExpand κ N (jqModC κ) = coeffMap (φpp κ p).toRingHom (qExpand κ N (jqModC κ))
  rw [coeffMap_qExpand, ← θ_symm_apply]
  congr 1
  rw [eq_comm, RingEquiv.symm_apply_eq]
  exact (θ_jqModC κ p).symm

end Laurent

section Restrict

variable (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] [PerfectRing κ p] (N : ℕ) [NeZero N]

theorem map_modularFunctionFieldC_toSubfield :
    (modularFunctionFieldC κ N).toSubfield.map (θ κ p).toRingHom = (modularFunctionFieldC κ N).toSubfield := by
  show (Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ {jqModC κ, jqNModC κ N})).map _ =
    Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ {jqModC κ, jqNModC κ N})
  rw [RingHom.map_field_closure, Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
  have h1 : ((θ κ p).toRingHom ∘ algebraMap κ (LaurentSeries κ)) = algebraMap κ (LaurentSeries κ) ∘ (φpp κ p).symm := by
    funext c; exact θ_algebraMap κ p c
  have h2 : Set.range (algebraMap κ (LaurentSeries κ) ∘ (φpp κ p).symm) = Set.range (algebraMap κ (LaurentSeries κ)) :=
    (φpp κ p).symm.surjective.range_comp _
  rw [h1, h2, show (θ κ p).toRingHom (jqModC κ) = jqModC κ from θ_jqModC κ p,
    show (θ κ p).toRingHom (jqNModC κ N) = jqNModC κ N from θ_jqNModC κ p N]

theorem mem_iff_θ_mem (x : LaurentSeries κ) : x ∈ modularFunctionFieldC κ N ↔ (θ κ p) x ∈ modularFunctionFieldC κ N := by
  constructor
  · intro hx
    have : (θ κ p) x ∈ (modularFunctionFieldC κ N).toSubfield.map (θ κ p).toRingHom :=
      Subfield.mem_map.mpr ⟨x, hx, rfl⟩
    rw [map_modularFunctionFieldC_toSubfield] at this
    exact this
  · intro hx
    have hx' : (θ κ p) x ∈ (modularFunctionFieldC κ N).toSubfield.map (θ κ p).toRingHom := by
      rw [map_modularFunctionFieldC_toSubfield]; exact hx
    obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp hx'
    have : y = x := (θ κ p).injective hyx
    exact this ▸ hy

theorem θ_symm_mem_iff (x : LaurentSeries κ) : (θ κ p).symm x ∈ modularFunctionFieldC κ N ↔ x ∈ modularFunctionFieldC κ N := by
  rw [mem_iff_θ_mem κ p N ((θ κ p).symm x), RingEquiv.apply_symm_apply]

noncomputable def θ₀ : ↥(modularFunctionFieldC κ N) ≃+* ↥(modularFunctionFieldC κ N) where
  toFun x := ⟨(θ κ p) x, (mem_iff_θ_mem κ p N _).1 x.2⟩
  invFun y := ⟨(θ κ p).symm y, (θ_symm_mem_iff κ p N _).2 y.2⟩
  left_inv x := Subtype.ext ((θ κ p).symm_apply_apply (x : LaurentSeries κ))
  right_inv y := Subtype.ext ((θ κ p).apply_symm_apply (y : LaurentSeries κ))
  map_mul' x y := Subtype.ext (map_mul (θ κ p) _ _)
  map_add' x y := Subtype.ext (map_add (θ κ p) _ _)

theorem coe_θ₀ (x : ↥(modularFunctionFieldC κ N)) : ((θ₀ κ p N x : ↥(modularFunctionFieldC κ N)) : LaurentSeries κ) = (θ κ p) x := rfl

theorem coe_θ₀_symm (x : ↥(modularFunctionFieldC κ N)) :
    (((θ₀ κ p N).symm x : ↥(modularFunctionFieldC κ N)) : LaurentSeries κ) = (θ κ p).symm x := rfl

theorem θ₀_symm_algebraMap (c : κ) :
    ∃ c' : κ, (θ₀ κ p N).symm (algebraMap κ ↥(modularFunctionFieldC κ N) c) = algebraMap κ ↥(modularFunctionFieldC κ N) c' := by
  refine ⟨φpp κ p c, Subtype.ext ?_⟩
  rw [coe_θ₀_symm]
  exact θ_symm_algebraMap κ p c

theorem existsUnique_place_read_qExpand (s : Place κ ↥(modularFunctionFieldC κ N)) :
    ∃! w : Place κ ↥(modularFunctionFieldC κ N),
      ∀ (g g' : ↥(modularFunctionFieldC κ N)),
        (g' : LaurentSeries κ) = qExpand κ (p * p) (g : LaurentSeries κ) →
        (g ∈ s.toValuationSubring ↔ g' ∈ w.toValuationSubring) := by
  have hpp : p * p ≠ 0 := mul_ne_zero (Fact.out : p.Prime).ne_zero (Fact.out : p.Prime).ne_zero
  refine ⟨transport (θ₀ κ p N) (θ₀_symm_algebraMap κ p N) s, ?_, ?_⟩
  · intro g g' hg'
    have hg'θ : g' = (θ₀ κ p N g) ^ (p * p) := by
      apply Subtype.ext
      rw [hg', qExpand_eq_θ_pow κ p]
      rfl
    rw [hg'θ, mem_transport_iff, map_pow, RingEquiv.symm_apply_apply, pow_mem_iff _ _ hpp]
  · intro w hw
    ext x
    have hx : ((x ^ (p * p) : ↥(modularFunctionFieldC κ N)) : LaurentSeries κ) =
        qExpand κ (p * p) (((θ₀ κ p N).symm x : ↥(modularFunctionFieldC κ N)) : LaurentSeries κ) := by
      rw [coe_θ₀_symm]
      exact pow_eq_qExpand_θ_symm κ p (x : LaurentSeries κ)
    have h1 := hw ((θ₀ κ p N).symm x) (x ^ (p * p)) hx
    rw [pow_mem_iff _ _ hpp] at h1
    rw [← h1, mem_transport_iff]

end Restrict

section Wrap

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem wrap {S T : IntermediateField K L} (hTS : T = S) (Rd : L → L) (s : Place K S)
    (h : ∃! w : Place K S, ∀ (g : S) (g' : S), (g' : L) = Rd g → (g ∈ s.toValuationSubring ↔ g' ∈ w.toValuationSubring)) :
    ∃! w : Place K T, ∀ (g : S) (g' : T), (g' : L) = Rd g → (g ∈ s.toValuationSubring ↔ g' ∈ w.toValuationSubring) := by
  subst hTS
  exact h

end Wrap

end RamZeroQ2

set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_qExpand ModularCurve.FullLevel IsLocalRing"

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hint : RingHom.IsIntegral (IntermediateField.inclusion hle).toRingHom)
    (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hs : s ∈ ssPlaces q M' (ResidueField A)) :
    ∃! w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      ∀ (g : ↥(modularFunctionFieldC (ResidueField A) M'))
        (g' : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        (g' : LaurentSeries (ResidueField A)) = qExpand (ResidueField A) (q ^ 2) (g : LaurentSeries (ResidueField A)) →
        (g ∈ s.toValuationSubring ↔ g' ∈ w.toValuationSubring) := by
  have hq' : q.Prime := Fact.out

  haveI hchar : CharP (ResidueField A) q := by
    rw [CharP.charP_iff_prime_eq_zero hq']
    have h0 : ((q : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by
      have : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by simp
      rw [this]; exact hA
    rw [ValuationSubring.coe_mem_nonunits_iff] at h0
    rw [← map_natCast (IsLocalRing.residue A) q]
    exact (IsLocalRing.residue_eq_zero_iff _).2 h0
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : ExpChar (ResidueField A) q := ExpChar.prime hq'
  haveI : PerfectRing (ResidueField A) q := inferInstance
  have heq := xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two q hq2 M' hqM' A hA
  have hsq : ∀ x : LaurentSeries (ResidueField A), qExpand (ResidueField A) (q ^ 2) x = qExpand (ResidueField A) (q * q) x :=
    fun x => qExpand_congr (sq q) x
  simp_rw [hsq]
  exact RamZeroQ2.wrap heq _ s (RamZeroQ2.existsUnique_place_read_qExpand (ResidueField A) q M' s)

end S_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two (solution)
