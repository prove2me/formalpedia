-- Prove2me | solution 1 for ModularCurve.exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8990bda9-453f-58d8-93aa-130fbb1025d9

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_kaehlerD_ne_zero_of_ord_eq_one
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_D_eq_smul_D_of_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct MatrixGroups

open KaehlerDifferential AlgebraicCurve

noncomputable section

namespace CartierLocalPen12

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf : f ≠ 0) (hmem : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) : 0 < v.ord f := by
  have h0 : 0 ≤ v.ord f := ord_nonneg_of_mem v hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso

    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    rw [← h, zpow_zero, mul_one] at hu
    have : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this] at hmax
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax u.isUnit

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) (hmem : f ∈ v.toValuationSubring) :
    (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

theorem coeff_unique {t : F} (hDt : D K F t ≠ 0) {g g' : F} (h : g • D K F t = g' • D K F t) : g = g' := by
  have h' : (g - g') • D K F t = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hDt

theorem exists_coeff [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (ω : Ω[F⁄K]) : ∃ c : F, ω = c • D K F t := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (D K F t) hDt).mp IsCurveOver.finrank_kaehler ω
  exact ⟨c, hc.symm⟩

noncomputable def deriv [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h : F) : F :=
  (exists_coeff hDt (D K F h)).choose

theorem D_eq_deriv_smul [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h : F) :
    D K F h = deriv hDt h • D K F t :=
  (exists_coeff hDt (D K F h)).choose_spec

theorem deriv_eq_of_D_eq [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) {h g : F} (hg : D K F h = g • D K F t) :
    deriv hDt h = g :=
  coeff_unique hDt ((D_eq_deriv_smul hDt h).symm.trans hg)

theorem deriv_add [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h h' : F) :
    deriv hDt (h + h') = deriv hDt h + deriv hDt h' :=
  deriv_eq_of_D_eq hDt (by rw [map_add, D_eq_deriv_smul hDt h, D_eq_deriv_smul hDt h', add_smul])

theorem deriv_zero [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) : deriv hDt (0 : F) = 0 :=
  deriv_eq_of_D_eq hDt (by rw [map_zero, zero_smul])

theorem deriv_sum [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → F) :
    deriv hDt (∑ i ∈ s, f i) = ∑ i ∈ s, deriv hDt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, deriv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, deriv_add, ih]

theorem deriv_pow_char_mul [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K F t ≠ 0)
    (a h : F) : deriv hDt (a ^ p * h) = a ^ p * deriv hDt h := by
  apply deriv_eq_of_D_eq hDt
  have hDap : D K F (a ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F p, CharP.cast_eq_zero F p, zero_smul]
  rw [Derivation.leibniz, hDap, smul_zero, add_zero, D_eq_deriv_smul hDt h, smul_smul]

theorem deriv_natCast_mul [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K F t ≠ 0)
    (m : ℕ) (h : F) : deriv hDt ((m : F) * h) = m * deriv hDt h := by
  have hm : ((m : F)) ^ p = m := by rw [← frobenius_def, map_natCast]
  rw [← hm, deriv_pow_char_mul p hDt, hm]

theorem deriv_t_pow [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (n : ℕ) :
    deriv hDt (t ^ n) = n * t ^ (n - 1) := by
  apply deriv_eq_of_D_eq hDt
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F n, smul_smul]

theorem deriv_iterate_pow_char_mul_t_pow [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K F t ≠ 0)
    (a : F) (k n : ℕ) :
    (deriv hDt)^[k] (a ^ p * t ^ n) = a ^ p * ((Nat.descFactorial n k : F) * t ^ (n - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, deriv_pow_char_mul p hDt, deriv_natCast_mul p hDt,
      deriv_t_pow hDt, Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul]
    ring

theorem iterate_deriv_sum [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (k : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → F) : (deriv hDt)^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, (deriv hDt)^[k] (f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, deriv_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Function.iterate_succ_apply' (deriv hDt)]

theorem ord_iterate_deriv_nonneg [IsCurveOver K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (hDt : D K F t ≠ 0) (k : ℕ) {h : F}
    (hh : 0 ≤ v.ord h) : 0 ≤ v.ord ((deriv hDt)^[k] h) := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact AlgebraicCurve.Place.ord_nonneg_of_D_eq_smul_D_of_ord_eq_one x v ht ih (D_eq_deriv_smul hDt _)

end CartierLocalPen12

namespace SigmaTransportPen12

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def Tw (σ : F →+* F) : Type _ := Ω[F⁄K]

variable (σ : F →+* F) (τ : K →+* K) (hστ : ∀ a : K, σ (algebraMap K F a) = algebraMap K F (τ a))

scoped instance : AddCommGroup (Tw (K := K) σ) := inferInstanceAs (AddCommGroup Ω[F⁄K])

def toTw : Ω[F⁄K] ≃+ Tw (K := K) σ := AddEquiv.refl _

scoped instance instModuleF : Module F (Tw (K := K) σ) := Module.compHom Ω[F⁄K] σ

scoped instance instModuleK : Module K (Tw (K := K) σ) := Module.compHom Ω[F⁄K] (σ.comp (algebraMap K F))

theorem smulF_def (f : F) (ω : Ω[F⁄K]) : (f • (toTw (K := K) σ ω) : Tw (K := K) σ) = toTw (K := K) σ (σ f • ω) := rfl

theorem smulK_def (a : K) (ω : Ω[F⁄K]) : (a • (toTw (K := K) σ ω) : Tw (K := K) σ) = toTw (K := K) σ (σ (algebraMap K F a) • ω) := rfl

scoped instance instTower : IsScalarTower K F (Tw (K := K) σ) :=
  ⟨fun a f ω => by
    change (toTw (K := K) σ) (σ (a • f) • (toTw (K := K) σ).symm ω) =
      (toTw (K := K) σ) (σ (algebraMap K F a) • (toTw (K := K) σ).symm ((toTw (K := K) σ) (σ f • (toTw (K := K) σ).symm ω)))
    rw [Algebra.smul_def, map_mul, mul_smul]
    rfl⟩

def twistD (hστ : ∀ a : K, σ (algebraMap K F a) = algebraMap K F (τ a)) : Derivation K F (Tw (K := K) σ) where
  toFun f := toTw (K := K) σ (D K F (σ f))
  map_add' f g := by rw [map_add, map_add, map_add]
  map_smul' a f := by
    rw [RingHom.id_apply, smulK_def, Algebra.smul_def, map_mul, Derivation.leibniz, hστ,
      Derivation.map_algebraMap, smul_zero, add_zero]
  map_one_eq_zero' := by
    show toTw (K := K) σ (D K F (σ 1)) = 0
    rw [map_one, Derivation.map_one_eq_zero]
    rfl
  leibniz' f g := by
    show toTw (K := K) σ (D K F (σ (f * g))) =
      f • toTw (K := K) σ (D K F (σ g)) + g • toTw (K := K) σ (D K F (σ f))
    rw [map_mul, Derivation.leibniz, smulF_def, smulF_def, ← map_add]

theorem twistD_apply (f : F) : twistD σ τ hστ f = toTw (K := K) σ (D K F (σ f)) := rfl

def transport : Ω[F⁄K] →+ Ω[F⁄K] :=
  ((toTw (K := K) σ).symm.toAddMonoidHom).comp ((twistD σ τ hστ).liftKaehlerDifferential).toAddMonoidHom

theorem transport_D (f : F) : transport σ τ hστ (D K F f) = D K F (σ f) := by
  show (toTw (K := K) σ).symm ((twistD σ τ hστ).liftKaehlerDifferential (D K F f)) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl

theorem transport_smul (f : F) (ω : Ω[F⁄K]) : transport σ τ hστ (f • ω) = σ f • transport σ τ hστ ω := by
  show (toTw (K := K) σ).symm ((twistD σ τ hστ).liftKaehlerDifferential (f • ω)) = _
  rw [LinearMap.map_smul]
  rfl

theorem transport_smul_D (f g : F) : transport σ τ hστ (f • D K F g) = σ f • D K F (σ g) := by
  rw [transport_smul, transport_D]

theorem transport_algebraMap_smul (a : K) (ω : Ω[F⁄K]) :
    transport σ τ hστ (a • ω) = τ a • transport σ τ hστ ω := by
  rw [← algebraMap_smul F a ω, transport_smul, hστ, algebraMap_smul]

end SigmaTransportPen12
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC.SigmaTransportPen12"

namespace SigmaTransportPen12

open ModularCurve

section Theta

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
  (Γ : Subgroup SL(2, ℤ))

def σF (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (Γ : Subgroup SL(2, ℤ)) : ↥(qExpFunctionFieldC K Γ) →+* ↥(qExpFunctionFieldC K Γ) :=
  MulSemiringAction.toRingHom (AlgebraicCurve.SemilinearAut K ↥(qExpFunctionFieldC K Γ)) ↥(qExpFunctionFieldC K Γ) (qExpArithFrobC p K Γ)

theorem σF_apply (x : ↥(qExpFunctionFieldC K Γ)) : σF K p Γ x = qExpArithFrobC p K Γ • x := by
  rfl

theorem coe_σF (x : ↥(qExpFunctionFieldC K Γ)) :
    ((σF K p Γ x : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap (frobenius K p) (x : LaurentSeries K) := by
  rw [σF_apply]; exact coe_qExpArithFrobC_smul p K Γ x

theorem σF_algebraMap (a : K) : σF K p Γ (algebraMap K _ a) = algebraMap K _ (frobenius K p a) := by
  rw [σF_apply, AlgebraicCurve.SemilinearAut.smul_def, AlgebraicCurve.SemilinearAut.commutes, baseAut_qExpArithFrobC_apply, frobenius_def]

def sigmaΩ (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (Γ : Subgroup SL(2, ℤ)) : Ω[↥(qExpFunctionFieldC K Γ)⁄K] →+ Ω[↥(qExpFunctionFieldC K Γ)⁄K] :=
  transport (σF K p Γ) (frobenius K p) (σF_algebraMap K p Γ)

theorem qEuler_coeffMap (τ : K →+* K) (s : LaurentSeries K) :
    qEuler K (coeffMap τ s) = coeffMap τ (qEuler K s) := by
  ext n
  rw [qEuler_coeff, coeffMap_coeff, coeffMap_coeff, qEuler_coeff, map_mul, map_intCast]

theorem diffQExp_sigmaΩ (ω : Ω[↥(qExpFunctionFieldC K Γ)⁄K]) :
    diffQExp (qExpFunctionFieldC K Γ) (sigmaΩ K p Γ ω) = coeffMap (frobenius K p) (diffQExp (qExpFunctionFieldC K Γ) ω) := by

  have key : ∀ ω ∈ Submodule.span (↥(qExpFunctionFieldC K Γ)) (Set.range (D K ↥(qExpFunctionFieldC K Γ))),
      diffQExp (qExpFunctionFieldC K Γ) (sigmaΩ K p Γ ω) = coeffMap (frobenius K p) (diffQExp (qExpFunctionFieldC K Γ) ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem ω h =>
      obtain ⟨g, rfl⟩ := h
      show diffQExp _ (transport _ _ _ (D K _ g)) = _
      rw [transport_D, diffQExp_D, diffQExp_D, coe_σF, qEuler_coeffMap]
    | zero => simp
    | add ω η _ _ hω hη => rw [map_add, map_add, map_add, map_add, hω, hη]
    | smul f ω _ hω =>
      have hω' : diffQExp (qExpFunctionFieldC K Γ) (transport (σF K p Γ) (frobenius K p) (σF_algebraMap K p Γ) ω) =
          coeffMap (frobenius K p) (diffQExp (qExpFunctionFieldC K Γ) ω) := hω
      show diffQExp _ (transport _ _ _ (f • ω)) = _
      rw [transport_smul, map_smul, map_smul]
      change ((σF K p Γ f : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) * diffQExp _ (transport (σF K p Γ) (frobenius K p) (σF_algebraMap K p Γ) ω) =
        coeffMap (frobenius K p) (((f : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) * diffQExp _ ω)
      rw [map_mul, ← coe_σF, hω']
  exact key ω (by rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top)

theorem coeff_diffQExp_sigmaΩ (ω : Ω[↥(qExpFunctionFieldC K Γ)⁄K]) (n : ℤ) :
    (diffQExp (qExpFunctionFieldC K Γ) (sigmaΩ K p Γ ω)).coeff n = ((diffQExp (qExpFunctionFieldC K Γ) ω).coeff n) ^ p := by
  rw [diffQExp_sigmaΩ, coeffMap_coeff, frobenius_def]

theorem sigmaΩ_algebraMap_smul (a : K) (ω : Ω[↥(qExpFunctionFieldC K Γ)⁄K]) :
    sigmaΩ K p Γ (a • ω) = (a ^ p) • sigmaΩ K p Γ ω := by
  show transport _ _ _ (a • ω) = _
  rw [transport_algebraMap_smul, frobenius_def]
  rfl

end Theta
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC.SigmaTransportPen12"

end SigmaTransportPen12
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC.SigmaTransportPen12"

namespace SigmaTransportPen12
open ModularCurve AlgebraicCurve HahnSeries

section FrobPlace
variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

omit [CharP K p] in
theorem qExpand_coeffMap {K' : Type*} [Field K'] (τ : K →+* K') (s : LaurentSeries K) :
    qExpand K' p (coeffMap τ s) = coeffMap τ (qExpand K p s) := by
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, coeffMap_coeff, coeffMap_coeff, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hk, coeffMap_coeff, qExpand_coeff_of_not_dvd p _ hk, map_zero]

variable [PerfectField K]

theorem qExpand_eq_coeffMap_symm_pow (s : LaurentSeries K) :
    qExpand K p s = (coeffMap ((frobeniusEquiv K p).symm : K →+* K) s) ^ p := by
  rw [pow_char_eq_coeffMap_frobenius_qExpand p, qExpand_coeffMap, coeffMap_coeffMap]
  have h : (frobenius K p).comp ((frobeniusEquiv K p).symm : K →+* K) = RingHom.id K :=
    RingHom.ext fun a => (frobeniusEquiv K p).apply_symm_apply a
  rw [h]
  ext k
  rw [coeffMap_coeff, RingHom.id_apply]

variable (Γ : Subgroup SL(2, ℤ))

theorem qExpFrobeniusModL_eq_inv_smul_pow (f : qExpFunctionFieldC K Γ) :
    qExpFrobeniusModL K Γ p f = ((qExpArithFrobC p K Γ)⁻¹ • f) ^ p := by
  apply Subtype.ext
  rw [coe_qExpFrobeniusModL, SubmonoidClass.coe_pow, SemilinearAut.inv_smul_def]
  exact qExpand_eq_coeffMap_symm_pow K p (f : LaurentSeries K)

theorem frob_eq_smul (w : Place K (qExpFunctionFieldC K Γ)) :
    qExpFrobeniusPlaceModL K Γ p w = qExpArithFrobC p K Γ • w :=
  Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow p (Fact.out : p.Prime).ne_zero
    (qExpArithFrobC p K Γ) (qExpFrobeniusModL K Γ p) (qExpFrobeniusModL_isIntegral K Γ p)
    (qExpFrobeniusModL_eq_inv_smul_pow K p Γ) w

omit [Fact p.Prime] [CharP K p] [PerfectField K] in
theorem hasValue_smul {F : Type*} [Field F] [Algebra K F] (g : SemilinearAut K F) (v : Place K F)
    {x : F} {a : K} (h : v.HasValue x a) : (g • v).HasValue (g • x) (SemilinearAut.baseAut g a) := by
  obtain ⟨hx, hres⟩ := h
  have hmem : g • x ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g x v.toValuationSubring hx
  refine ⟨hmem, ?_⟩
  have key : IsLocalRing.residue (g • v).toValuationSubring
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩) =
      SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  have hx' : (⟨g • x, hmem⟩ : (g • v).toValuationSubring) =
      SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩ := rfl
  rw [hx', key, hres, SemilinearAut.smulResidueRingEquiv_algebraMap]

omit [Fact p.Prime] [CharP K p] [PerfectField K] in
theorem smul_mem_smul {F : Type*} [Field F] [Algebra K F] (g : SemilinearAut K F) (v : Place K F)
    {x : F} (hx : x ∈ v.toValuationSubring) : g • x ∈ (g • v).toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.smul_mem_pointwise_smul g x v.toValuationSubring hx

end FrobPlace
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC.SigmaTransportPen12"
end SigmaTransportPen12
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC.SigmaTransportPen12"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC.SigmaTransportPen12"

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    ∃ σΩ : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K] →+ Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K],
      (∀ (a : K) (ω : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]), σΩ (a • ω) = (a ^ p) • σΩ ω) ∧
      (∀ (ω : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]) (n : ℤ),
        (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ) (σΩ ω)).coeff n = ((ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ) ω).coeff n) ^ p) ∧
      (∀ (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)) (ω : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K]),
        (v.IsRegularAt ω → (ModularCurve.qExpFrobeniusPlaceModL K Γ p v).IsRegularAt (σΩ ω)) ∧
        (v.HasSimplePoleAt ω → (ModularCurve.qExpFrobeniusPlaceModL K Γ p v).HasSimplePoleAt (σΩ ω)) ∧
        (∀ r : K, v.HasSimpleResidue ω r → (ModularCurve.qExpFrobeniusPlaceModL K Γ p v).HasSimpleResidue (σΩ ω) (r ^ p))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨x, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  haveI := hfd
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set ↥(ModularCurve.qExpFunctionFieldC K Γ))) ↥(ModularCurve.qExpFunctionFieldC K Γ) := Algebra.IsAlgebraic.of_finite _ _
  refine ⟨SigmaTransportPen12.sigmaΩ K p Γ, SigmaTransportPen12.sigmaΩ_algebraMap_smul K p Γ,
    SigmaTransportPen12.coeff_diffQExp_sigmaΩ K p Γ, ?_⟩
  intro v ω

  set g := ModularCurve.qExpArithFrobC p K Γ with hgdef
  have hw : ModularCurve.qExpFrobeniusPlaceModL K Γ p v = g • v := SigmaTransportPen12.frob_eq_smul K p Γ v
  rw [hw]
  set w := g • v with hwdef

  set t := v.uniformizer with htdef
  set t' := w.uniformizer with ht'def
  have ht : v.ord t = 1 := v.ord_uniformizer
  have ht' : w.ord t' = 1 := w.ord_uniformizer
  have ht0 : t ≠ 0 := v.uniformizer_ne_zero
  have ht'0 : t' ≠ 0 := w.uniformizer_ne_zero
  have hdc : v.dCoord = D K ↥(ModularCurve.qExpFunctionFieldC K Γ) t := v.dCoord_eq
  have hdc' : w.dCoord = D K ↥(ModularCurve.qExpFunctionFieldC K Γ) t' := w.dCoord_eq
  have hDt' : D K ↥(ModularCurve.qExpFunctionFieldC K Γ) t' ≠ 0 := AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one x w ht'
  have ht'mem : t' ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w (by rw [ht']; exact zero_le_one)

  have hσΩ : ∀ f h : ↥(ModularCurve.qExpFunctionFieldC K Γ), SigmaTransportPen12.sigmaΩ K p Γ (f • D K ↥(ModularCurve.qExpFunctionFieldC K Γ) h) = (g • f) • D K ↥(ModularCurve.qExpFunctionFieldC K Γ) (g • h) := by
    intro f h
    show SigmaTransportPen12.transport _ _ _ (f • D K _ h) = _
    rw [SigmaTransportPen12.transport_smul_D, SigmaTransportPen12.σF_apply, SigmaTransportPen12.σF_apply]

  have hgt0 : g • t ≠ 0 := by
    intro h0; apply ht0
    have := congrArg (fun y => g⁻¹ • y) h0
    simpa using this
  have hσt_ord : w.ord (g • t) = 1 := by rw [hwdef, AlgebraicCurve.SemilinearAut.ord_smul]; exact ht
  set u : ↥(ModularCurve.qExpFunctionFieldC K Γ) := (g • t) * t'⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hgt0 (inv_ne_zero ht'0)
  have hu_ord : w.ord u = 0 := by rw [hudef, w.ord_mul hgt0 (inv_ne_zero ht'0), w.ord_inv, hσt_ord, ht']; ring
  have hu_mem : u ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w (by rw [hu_ord])
  have huinv_mem : u⁻¹ ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w (by rw [w.ord_inv, hu_ord, neg_zero])
  have hgt : g • t = u * t' := by rw [hudef, mul_assoc, inv_mul_cancel₀ ht'0, mul_one]

  obtain ⟨u', hu'⟩ := CartierLocalPen12.exists_coeff hDt' (D K ↥(ModularCurve.qExpFunctionFieldC K Γ) u)
  have hu'_ord : 0 ≤ w.ord u' :=
    AlgebraicCurve.Place.ord_nonneg_of_D_eq_smul_D_of_ord_eq_one x w ht' (by rw [hu_ord]) hu'
  have hu'_mem : u' ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w hu'_ord
  set c : ↥(ModularCurve.qExpFunctionFieldC K Γ) := u + t' * u' with hcdef
  have hDgt : D K ↥(ModularCurve.qExpFunctionFieldC K Γ) (g • t) = c • D K ↥(ModularCurve.qExpFunctionFieldC K Γ) t' := by
    rw [hgt, Derivation.leibniz, hu', smul_smul, ← add_smul, hcdef, add_comm, mul_comm t' u']
  have hc_mem : c ∈ w.toValuationSubring := add_mem hu_mem (mul_mem ht'mem hu'_mem)

  have hmaster : ∀ f : ↥(ModularCurve.qExpFunctionFieldC K Γ), SigmaTransportPen12.sigmaΩ K p Γ (f • v.dCoord) = ((g • f) * c) • w.dCoord := by
    intro f
    rw [hdc, hσΩ, hDgt, smul_smul, hdc']
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨f, hf, rfl⟩
    exact ⟨(g • f) * c, mul_mem (SigmaTransportPen12.smul_mem_smul K g v hf) hc_mem, hmaster f⟩
  ·
    rintro ⟨f, htf, rfl⟩
    refine ⟨(g • f) * c, ?_, hmaster f⟩

    have e : t' * ((g • f) * c) = u⁻¹ * (g • (t * f)) * c := by
      rw [smul_mul', hgt]
      field_simp
      try ring
    rw [e]
    exact mul_mem (mul_mem huinv_mem (SigmaTransportPen12.smul_mem_smul K g v htf)) hc_mem
  ·
    rintro r ⟨f, rfl, hval⟩
    refine ⟨(g • f) * c, hmaster f, ?_⟩
    have hv' := SigmaTransportPen12.hasValue_smul K g v hval
    rw [ModularCurve.baseAut_qExpArithFrobC_apply] at hv'

    have e : t' * ((g • f) * c) = (g • (t * f)) * (1 + t' * u' * u⁻¹) := by
      rw [smul_mul', hgt, hcdef]
      field_simp
      try ring
    rw [e]
    obtain ⟨hm1, hr1⟩ := hv'
    have hm2 : (1 + t' * u' * u⁻¹ : ↥(ModularCurve.qExpFunctionFieldC K Γ)) ∈ w.toValuationSubring :=
      add_mem (one_mem _) (mul_mem (mul_mem ht'mem hu'_mem) huinv_mem)
    refine ⟨mul_mem hm1 hm2, ?_⟩
    have hmax : (⟨t' * u' * u⁻¹, mul_mem (mul_mem ht'mem hu'_mem) huinv_mem⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring := by
      by_cases h0 : u' = 0
      · have : (⟨t' * u' * u⁻¹, mul_mem (mul_mem ht'mem hu'_mem) huinv_mem⟩ : w.toValuationSubring) = 0 :=
          Subtype.ext (by simp [h0])
        rw [this]; exact Ideal.zero_mem _
      · refine CartierLocalPen12.mem_maximalIdeal_of_ord_pos w ?_ _
        rw [w.ord_mul (mul_ne_zero ht'0 h0) (inv_ne_zero hu0), w.ord_mul ht'0 h0, ht', w.ord_inv, hu_ord]
        omega
    have hres2 : IsLocalRing.residue w.toValuationSubring ⟨1 + t' * u' * u⁻¹, hm2⟩ = 1 := by
      have : (⟨1 + t' * u' * u⁻¹, hm2⟩ : w.toValuationSubring) = 1 + ⟨t' * u' * u⁻¹, mul_mem (mul_mem ht'mem hu'_mem) huinv_mem⟩ :=
        Subtype.ext rfl
      rw [this, map_add, map_one, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, add_zero]
    have hmul : (⟨g • (t * f) * (1 + t' * u' * u⁻¹), mul_mem hm1 hm2⟩ : w.toValuationSubring) =
        ⟨g • (t * f), hm1⟩ * ⟨1 + t' * u' * u⁻¹, hm2⟩ := Subtype.ext rfl
    rw [hmul, map_mul, hr1, hres2, mul_one]

end S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC (solution)
