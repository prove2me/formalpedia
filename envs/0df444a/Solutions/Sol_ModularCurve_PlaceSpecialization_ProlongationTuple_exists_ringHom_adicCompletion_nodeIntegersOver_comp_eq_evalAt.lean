-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ec085f42-e01f-59ca-bc13-e6fe8ce916f6

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
import Theorems.Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic
import Theorems.Thm_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
import Theorems.Thm_Valued_forall_exists_pow_le_comap_span_singleton_pow_of_eq_span
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

open _root_.AdicCompletion Valued in
section
set_option maxHeartbeats 1600000

namespace AdicCompletion
p2m_export "AdicCompletion" "map eval eval_of of mk_surjective map_zero ext algebraMap_apply isAdicComplete pow_smul_top_eq_ker_eval subring exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap"
namespace Units
p2m_open "AdicCompletion"

variable {B : Type*} [CommRing B] (I : Ideal B)

local notation "Bh" => AdicCompletion I B

theorem mul_mem_pow_smul_top {n : ℕ} (z : Bh) {t : Bh} (ht : t ∈ (I ^ n • ⊤ : Submodule B Bh)) :
    z * t ∈ (I ^ n • ⊤ : Submodule B Bh) := by
  refine Submodule.smul_induction_on (p := fun t => z * t ∈ (I ^ n • ⊤ : Submodule B Bh)) ht ?_ ?_
  · intro r hr m _
    change z * (r • m) ∈ _
    rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    change z * (x + y) ∈ _
    rw [mul_add]; exact add_mem hx hy

theorem mul_mem_pow_smul_top_add {a b : ℕ} {u t : Bh} (hu : u ∈ (I ^ a • ⊤ : Submodule B Bh))
    (ht : t ∈ (I ^ b • ⊤ : Submodule B Bh)) : u * t ∈ (I ^ (a + b) • ⊤ : Submodule B Bh) := by
  refine Submodule.smul_induction_on (p := fun u => u * t ∈ (I ^ (a + b) • ⊤ : Submodule B Bh)) hu ?_ ?_
  · intro r hr m _
    change (r • m) * t ∈ _
    rw [smul_mul_assoc, pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_mem_pow_smul_top I m ht)
  · intro x y hx hy
    change (x + y) * t ∈ _
    rw [add_mul]; exact add_mem hx hy

theorem mul_mem_smul_top (z : Bh) {t : Bh} (ht : t ∈ (I • ⊤ : Submodule B Bh)) :
    z * t ∈ (I • ⊤ : Submodule B Bh) := by
  refine Submodule.smul_induction_on (p := fun t => z * t ∈ (I • ⊤ : Submodule B Bh)) ht ?_ ?_
  · intro r hr m _
    change z * (r • m) ∈ _
    rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    change z * (x + y) ∈ _
    rw [mul_add]; exact add_mem hx hy

theorem mul_mem_pow_smul_top_succ {a : ℕ} {u y : Bh} (hu : u ∈ (I ^ a • ⊤ : Submodule B Bh))
    (hy : y ∈ (I • ⊤ : Submodule B Bh)) : u * y ∈ (I ^ (a + 1) • ⊤ : Submodule B Bh) := by
  have hpow : I ^ (a + 1) = I ^ a * I := pow_succ I a
  rw [hpow, Submodule.mul_smul]
  refine Submodule.smul_induction_on (p := fun u => u * y ∈ (I ^ a • (I • ⊤ : Submodule B Bh) : Submodule B Bh)) hu ?_ ?_
  · intro r hr m _
    change (r • m) * y ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr (mul_mem_smul_top I m hy)
  · intro x z hx hz
    change (x + z) * y ∈ _
    rw [add_mul]; exact add_mem hx hz

theorem pow_mem_pow_smul_top {y : Bh} (hy : y ∈ (I • ⊤ : Submodule B Bh)) (i : ℕ) :
    y ^ i ∈ (I ^ i • ⊤ : Submodule B Bh) := by
  induction i with
  | zero => simp [Ideal.map_top]
  | succ i ih =>
    have hy' : y ^ (i + 1) = y ^ i * y := pow_succ y i
    rw [hy']
    exact mul_mem_pow_smul_top_succ I ih hy

theorem isUnit_one_sub (hI : I.FG) {y : Bh} (hy : y ∈ (I • ⊤ : Submodule B Bh)) : IsUnit (1 - y) := by
  haveI : IsAdicComplete I Bh := AdicCompletion.isAdicComplete hI

  let s : ℕ → Bh := fun m => ∑ i ∈ Finset.range m, y ^ i
  have hs : ∀ {m n : ℕ}, m ≤ n → s m ≡ s n [SMOD (I ^ m • ⊤ : Submodule B Bh)] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have : s m - s n = -∑ i ∈ Finset.Ico m n, y ^ i := by
      simp only [s]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
    rw [this]
    refine neg_mem (Submodule.sum_mem _ fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hi.1) (pow_mem_pow_smul_top I hy i)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I) (M := Bh)) hs

  have hkey : (1 - y) * L = 1 := by
    apply eq_of_sub_eq_zero
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := Bh))
    intro m
    have h1 : (1 - y) * s m = 1 - y ^ m := mul_neg_geom_sum y m
    have e : (1 - y) * L - 1 = (1 - y) * (L - s m) - y ^ m := by rw [mul_sub, h1]; ring
    rw [SModEq.zero, e]
    refine sub_mem (mul_mem_pow_smul_top I _ ?_) (pow_mem_pow_smul_top I hy m)
    have := SModEq.sub_mem.mp (hL m)
    rw [← neg_sub] ; exact neg_mem this
  exact IsUnit.of_mul_eq_one L hkey

end AdicCompletion.Units

namespace AdicCompletion
p2m_export "AdicCompletion" "map eval eval_of of mk_surjective map_zero ext algebraMap_apply isAdicComplete pow_smul_top_eq_ker_eval subring exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap"
namespace Units
p2m_open "AdicCompletion"

open Valued

variable {B : Type*} [CommRing B] [IsLocalRing B]
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hK : Valued K Γ₀]

theorem v_eq_one_of_isUnit {s : 𝒪[K]} (hs : IsUnit s) : Valued.v (s : K) = 1 := by
  obtain ⟨u, rfl⟩ := hs
  have hprod : Valued.v ((u : 𝒪[K]) : K) * Valued.v ((↑u⁻¹ : 𝒪[K]) : K) = 1 := by
    rw [← Valuation.map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, Valuation.map_one]
  refine le_antisymm u.1.2 ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v ((u : 𝒪[K]) : K) * Valued.v ((↑u⁻¹ : 𝒪[K]) : K) < 1 :=
    calc _ ≤ Valued.v ((u : 𝒪[K]) : K) * 1 := mul_le_mul_right (↑u⁻¹ : 𝒪[K]).2 _
      _ < 1 := by rw [mul_one]; exact hlt
  rw [hprod] at this
  exact (lt_irrefl _) this

theorem isLocalHom_of_forall_mem_maximalIdeal (hFG : (IsLocalRing.maximalIdeal B).FG)
    (ψ : AdicCompletion (IsLocalRing.maximalIdeal B) B →+* 𝒪[K])
    (hψ : ∀ r ∈ IsLocalRing.maximalIdeal B, Valued.v ((ψ (algebraMap B _ r) : 𝒪[K]) : K) < 1) :
    IsLocalHom ψ := by
  refine ⟨fun z hz => ?_⟩

  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (IsLocalRing.maximalIdeal B) B 1 z)
  have hzb : z - algebraMap B _ b ∈ ((IsLocalRing.maximalIdeal B) ^ 1 • ⊤ :
      Submodule B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hFG, LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.eval_of, Submodule.mkQ_apply, hb, sub_self]
  rw [pow_one] at hzb

  have hsmall : ∀ y ∈ ((IsLocalRing.maximalIdeal B) • ⊤ : Submodule B (AdicCompletion (IsLocalRing.maximalIdeal B) B)),
      Valued.v ((ψ y : 𝒪[K]) : K) < 1 := by
    intro y hy
    refine Submodule.smul_induction_on (p := fun y => Valued.v ((ψ y : 𝒪[K]) : K) < 1) hy ?_ ?_
    · intro r hr m _
      change Valued.v ((ψ (r • m) : 𝒪[K]) : K) < 1
      rw [Algebra.smul_def, map_mul, Subring.coe_mul, Valuation.map_mul]
      calc Valued.v ((ψ (algebraMap B _ r) : 𝒪[K]) : K) * Valued.v ((ψ m : 𝒪[K]) : K)
          ≤ Valued.v ((ψ (algebraMap B _ r) : 𝒪[K]) : K) * 1 := mul_le_mul_right (ψ m).2 _
        _ < 1 := by rw [mul_one]; exact hψ r hr
    · intro x y hx hy
      change Valued.v ((ψ (x + y) : 𝒪[K]) : K) < 1
      rw [map_add, Subring.coe_add]
      exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt hx hy)

  have hbunit : IsUnit b := by
    by_contra hbn
    have hbm : b ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hbn)
    have e : z = (z - algebraMap B _ b) + algebraMap B _ b := by ring
    have hlt : Valued.v ((ψ z : 𝒪[K]) : K) < 1 := by
      rw [e, map_add, Subring.coe_add]
      exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt (hsmall _ hzb) (hψ b hbm))
    rw [v_eq_one_of_isUnit hz] at hlt
    exact (lt_irrefl _) hlt

  obtain ⟨ub, hub⟩ := (hbunit.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)))
  have e2 : z = ub * (1 - (-(↑ub⁻¹ * (z - algebraMap B _ b)))) := by
    rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hub]; ring
  rw [e2]
  exact (Units.isUnit ub).mul (isUnit_one_sub _ hFG (neg_mem (mul_mem_smul_top _ _ hzb)))

end AdicCompletion.Units

end

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place.isRational_iff_deg_eq_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext toValuationSubring IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt evalAt_one evalAt_algebraMap isRational_iff_deg_eq_one evalAt_mul"
namespace CE2
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem evalAt_add_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_zero_eq : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), v.evalAt_algebraMap]

noncomputable def evalRingHom (hv : v.IsRational) (B : Subring F) (hB : ∀ g ∈ B, g ∈ v.toValuationSubring) :
    B →+* K where
  toFun g := v.evalAt (g : F)
  map_one' := by rw [OneMemClass.coe_one, v.evalAt_one]
  map_mul' a b := by rw [MulMemClass.coe_mul, v.evalAt_mul hv (hB _ a.2) (hB _ b.2)]
  map_zero' := by rw [ZeroMemClass.coe_zero, evalAt_zero_eq]
  map_add' a b := by rw [AddMemClass.coe_add, evalAt_add_of_mem v hv (hB _ a.2) (hB _ b.2)]

theorem evalRingHom_apply (hv : v.IsRational) (B : Subring F) (hB : ∀ g ∈ B, g ∈ v.toValuationSubring) (g : B) :
    evalRingHom v hv B hB g = v.evalAt (g : F) := rfl

end AlgebraicCurve.Place.CE2

theorem pow_mul_le_pow_of_pow_eq_zpow {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a θ : Γ₀}
    (hθ0 : θ ≠ 0) (hθ1 : θ < 1) (ha1 : a < 1) {m : ℕ} (hm : 0 < m) {j : ℤ} (h : a ^ m = θ ^ j) (k : ℕ) :
    a ^ (m * k) ≤ θ ^ k := by

  have hj : 1 ≤ j := by
    by_contra hle
    push Not at hle
    have : 1 ≤ θ ^ j := one_le_zpow_of_nonpos₀ (zero_lt_iff.mpr hθ0) hθ1.le (by omega)
    rw [← h] at this
    exact (lt_irrefl _) (this.trans_lt (pow_lt_one₀ zero_le' ha1 (by omega)))
  obtain ⟨J, hJ⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ j)
  have hJ1 : 1 ≤ J := by omega
  rw [pow_mul, h, hJ, zpow_natCast, ← pow_mul]
  exact pow_le_pow_right_of_le_one' hθ1.le (Nat.le_mul_of_pos_left k (by omega))

set_option maxHeartbeats 3200000 in
open Valued AlgebraicCurve.Place.CE2 ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hVI : R.ValueIntegralityLaw w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+*
        𝒪[(A.valuation).Completion],
      IsLocalHom ψ ∧ ∀ g : ↥(R.nodeIntegersOver K w),
        ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ((V.evalAt (g : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion) := by
  classical

  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  have hVr : V.IsRational := (Place.isRational_iff_deg_eq_one V).2 (IsCurveOver.deg_eq_one_of_isAlgClosed V)

  obtain ⟨ιC, hιC, hvC⟩ : ∃ ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion,
      (∀ x, ιC x = (x : (A.valuation).Completion)) ∧ ∀ x, Valued.v (ιC x) = A.valuation x := by
    refine ⟨(UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* (A.valuation).Completion).comp
      (WithVal.equiv A.valuation).symm.toRingHom, fun x => rfl, fun x => ?_⟩
    show Valued.v (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : (A.valuation).Completion) = A.valuation x
    rw [Valued.valuedCompletion_apply]
    rfl

  obtain ⟨evO, hevO⟩ : ∃ evO : ↥(R.nodeIntegersOver K w) →+* 𝒪[(A.valuation).Completion],
      ∀ b, ((evO b : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        ιC (V.evalAt (b : ↥(modularFunctionFieldBar (N * q)))) := by
    let ev := evalRingHom V hVr (R.nodeIntegersOver K w) (fun g hg => hg.1.2.2 V hV)
    have hmemO : ∀ b : ↥(R.nodeIntegersOver K w), (ιC.comp ev) b ∈ 𝒪[(A.valuation).Completion] := by
      intro b
      change Valued.v (ιC (ev b)) ≤ 1
      rw [hvC]
      exact A.valuation_le_one ⟨_, hVI _ b.2.1 V hV⟩
    exact ⟨(ιC.comp ev).codRestrict _ hmemO, fun b => rfl⟩
  have hvalO : ∀ b : ↥(R.nodeIntegersOver K w), Valued.v ((evO b : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)
      = A.valuation (V.evalAt (b : ↥(modularFunctionFieldBar (N * q)))) := fun b => by rw [hevO, hvC]

  have hvϖ1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 :=
    valuation_coe_lt_one_of_maximalIdeal_eq_span R K w c ϖ hmax
  have hϖ0' : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hvϖ0 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
    rwa [Valuation.ne_zero_iff]
  obtain ⟨ϖC, hϖC⟩ : ∃ ϖC : 𝒪[(A.valuation).Completion],
      (ϖC : (A.valuation).Completion) = ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) :=
    ⟨⟨ιC _, by change Valued.v (ιC _) ≤ 1; rw [hvC]; exact hvϖ1.le⟩, rfl⟩
  have hvϖC : Valued.v (ϖC : (A.valuation).Completion) =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [hϖC, hvC]
  have hϖC0 : (ϖC : (A.valuation).Completion) ≠ 0 := by
    rw [hϖC]; exact (map_ne_zero ιC).mpr hϖ0'

  haveI : IsAdicComplete (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion] := by
    apply Valued.isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt ϖC hϖC0
    intro γ hγ
    rw [hvϖC]
    exact A.exists_valuation_pow_lt_of_isAlgebraic hvϖ0 hvϖ1 γ hγ

  have hmem₁ : R.nodeConst K w ϖ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rw [hmax]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hmem₂ : c.x ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rw [hmax]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hmem₃ : c.y ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rw [hmax]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hval : ∀ g : ↥(R.nodeIntegersOver K w), g ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) →
      Valued.v ((evO g : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) < 1 := by
    intro g hg
    rw [hvalO]
    exact (valuation_evalAt_lt_one_iff_mem_maximalIdeal R K w hVI V hV g).mpr hg

  have harch_g : ∀ g : ↥(R.nodeIntegersOver K w), g ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) →
      ∀ k' : ℕ, ∃ n : ℕ, Valued.v ((evO g : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) ^ n ≤
        Valued.v (ϖC : (A.valuation).Completion) ^ k' := by
    intro g hg k'
    rw [hvalO, hvϖC]
    by_cases h0 : V.evalAt (g : ↥(modularFunctionFieldBar (N * q))) = 0
    · refine ⟨1, ?_⟩
      rw [h0, Valuation.map_zero, pow_one]
      exact zero_le'
    · obtain ⟨m, hm, j, hj⟩ := A.exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic hvϖ0 hvϖ1 h0
      refine ⟨m * k', ?_⟩
      have hlt := hval g hg
      rw [hvalO] at hlt
      exact pow_mul_le_pow_of_pow_eq_zpow hvϖ0 hvϖ1 hlt hm hj k'

  have harchδ : ∀ k' : ℕ, ∃ n : ℕ,
      (max (max (Valued.v ((evO (R.nodeConst K w ϖ) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion))
        (Valued.v ((evO c.x : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)))
        (Valued.v ((evO c.y : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion))) ^ n ≤
      Valued.v (ϖC : (A.valuation).Completion) ^ k' := by
    intro k'
    obtain ⟨n₁, hn₁⟩ := harch_g (R.nodeConst K w ϖ) hmem₁ k'
    obtain ⟨n₂, hn₂⟩ := harch_g c.x hmem₂ k'
    obtain ⟨n₃, hn₃⟩ := harch_g c.y hmem₃ k'
    refine ⟨max (max n₁ n₂) n₃, ?_⟩
    have key : ∀ (a : _) (n : ℕ), a ≤ 1 → a ^ n ≤ Valued.v (ϖC : (A.valuation).Completion) ^ k' →
        n ≤ max (max n₁ n₂) n₃ → a ^ (max (max n₁ n₂) n₃) ≤ Valued.v (ϖC : (A.valuation).Completion) ^ k' :=
      fun a n ha h hn => (pow_le_pow_right_of_le_one' ha hn).trans h
    have hle : ∀ b : ↥(R.nodeIntegersOver K w),
        Valued.v ((evO b : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) ≤ 1 := fun b => (evO b).2
    rcases max_cases (max (Valued.v ((evO (R.nodeConst K w ϖ) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion))
        (Valued.v ((evO c.x : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)))
        (Valued.v ((evO c.y : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      rcases max_cases (Valued.v ((evO (R.nodeConst K w ϖ) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion))
          (Valued.v ((evO c.x : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) with ⟨h', -⟩ | ⟨h', -⟩
      · rw [h']; exact key _ _ (hle _) hn₁ (by omega)
      · rw [h']; exact key _ _ (hle _) hn₂ (by omega)
    · rw [h]; exact key _ _ (hle _) hn₃ (by omega)
  have hδle : ∀ g ∈ ({R.nodeConst K w ϖ, c.x, c.y} : Set ↥(R.nodeIntegersOver K w)),
      Valued.v ((evO g : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) ≤
        max (max (Valued.v ((evO (R.nodeConst K w ϖ) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion))
          (Valued.v ((evO c.x : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)))
          (Valued.v ((evO c.y : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  have hcont := Valued.forall_exists_pow_le_comap_span_singleton_pow_of_eq_span
    (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) evO {R.nodeConst K w ϖ, c.x, c.y} hmax _ hδle ϖC hϖC0 harchδ
  obtain ⟨ψ, hψ⟩ := AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
    (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) (Ideal.span {ϖC}) evO hcont
  have hψg : ∀ g : ↥(R.nodeIntegersOver K w), ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g) = evO g := fun g => by
    rw [← RingHom.comp_apply, hψ]
  have hFG : (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)).FG :=
    ⟨{R.nodeConst K w ϖ, c.x, c.y}, by rw [hmax]; simp⟩
  exact ⟨ψ, AdicCompletion.Units.isLocalHom_of_forall_mem_maximalIdeal hFG ψ
    (fun r hr => by rw [hψg]; exact hval r hr), fun g => by rw [hψg, hevO, hιC]⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt (solution)
