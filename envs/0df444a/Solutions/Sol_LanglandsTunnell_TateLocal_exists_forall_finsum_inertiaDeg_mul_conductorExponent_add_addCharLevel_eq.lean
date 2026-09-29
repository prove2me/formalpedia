-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/95784915-a099-5abe-90d6-774a9b0b1139

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal"

section T2sec

open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel higherUnitsAt mem_higherUnitsAt_iff HasConductorExponentAt hasConductorExponentAt_unique forall_eq_one_and_exists_ne_one_of_addCharLevel addCharLevel_psiLocal_rat psiLocal_ne_one psiLocal_eq_one_of_mem_integers"
namespace NormTraceSecondOrder
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 ℚ)) (P : w.Extension (𝓞 K))

set_option quotPrecheck false
local notation "Zw" => w.adicCompletionIntegers ℚ
local notation "OP" => (Subtype.val P).adicCompletionIntegers K
local notation "Qw" => w.adicCompletion ℚ
local notation "KP" => (Subtype.val P).adicCompletion K

private theorem valued_algebraMap (x : Qw) :
    Valued.v (algebraMap Qw KP x) = Valued.v x ^ w.asIdeal.ramificationIdx' P.1.asIdeal := by
  show Valued.v (Extension.adicCompletionSemialgHom ℚ K P x) = _
  rw [Extension.valued_adicCompletionSemialgHom]
  have h : (P.1.under (𝓞 ℚ)).asIdeal = w.asIdeal := by rw [P.2]
  rw [h]

private theorem one_le_ramificationIdx : 1 ≤ w.asIdeal.ramificationIdx' P.1.asIdeal := by
  have h : (P.1.under (𝓞 ℚ)).asIdeal = w.asIdeal := by rw [P.2]
  rw [← h]
  exact Nat.one_le_iff_ne_zero.mpr
    (ramificationIdx_ne_zero (𝓞 ℚ) (𝓞 K) (algebraMap_injective_of_field_isFractionRing (𝓞 ℚ) (𝓞 K) ℚ K) P.1)

private scoped instance instIsScalarTower_int : IsScalarTower Zw OP KP := .of_algebraMap_smul fun _ _ ↦ rfl

private scoped instance instIsScalarTower_int' : IsScalarTower Zw Qw KP := .of_algebraMap_smul fun _ _ ↦ rfl

private theorem algebraMap_int_injective : Function.Injective (algebraMap Zw OP) := by
  intro x y h
  have : (algebraMap Zw KP x) = algebraMap Zw KP y := by
    rw [IsScalarTower.algebraMap_apply Zw OP KP, h, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply Zw Qw KP, IsScalarTower.algebraMap_apply Zw Qw KP] at this
  exact Subtype.val_injective ((algebraMap Qw KP).injective this)

private scoped instance instIsTorsionFree_int : Module.IsTorsionFree Zw OP := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact algebraMap_int_injective K w P

private noncomputable scoped instance instFree_int : Module.Free Zw OP := Module.free_of_finite_type_torsion_free'

private noncomputable def unif : Zw := (adicCompletion.exists_uniformizer ℚ w).choose

private theorem valued_unif : Valued.v ((unif w : Zw) : Qw) = WithZero.exp (-1 : ℤ) :=
  (adicCompletion.exists_uniformizer ℚ w).choose_spec

private theorem valued_algebraMap_unif :
    Valued.v (algebraMap Qw KP (unif w : Zw)) = WithZero.exp (-(w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ)) := by
  rw [valued_algebraMap, valued_unif, ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul, mul_one]

private theorem algebraMap_unif_ne_zero : algebraMap Qw KP (unif w : Zw) ≠ 0 := by
  intro h0
  have h := valued_algebraMap_unif K w P
  rw [h0, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

private theorem unif_ne_zero : (unif w : Zw) ≠ 0 := by
  intro h0
  have h := valued_unif w
  rw [h0, ZeroMemClass.coe_zero, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

private theorem exists_pow_mul_mem_integers (y : KP) :
    ∃ k : ℕ, Valued.v ((algebraMap Qw KP (unif w : Zw)) ^ k * y) ≤ 1 := by
  by_cases hy : Valued.v y = 0
  · exact ⟨0, by simp [hy]⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v y = WithZero.exp n := ⟨_, (WithZero.coe_unzero hy).symm⟩
    refine ⟨n.toNat, ?_⟩
    rw [map_mul, map_pow, valued_algebraMap_unif, hn, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp, smul_neg, nsmul_eq_mul]
    have h1 := Int.self_le_toNat n
    have h2 : (n.toNat : ℤ) ≤ (n.toNat : ℤ) * (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) :=
      le_mul_of_one_le_right (Int.natCast_nonneg _) (by exact_mod_cast one_le_ramificationIdx K w P)
    linarith

private noncomputable scoped instance instIsLocalization_int : IsLocalization (Algebra.algebraMapSubmonoid OP (Zw⁰)) KP where
  map_units := by
    rintro ⟨s, hs⟩
    obtain ⟨r, hr, rfl⟩ := hs
    apply IsUnit.mk0
    intro h0
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    apply hr0
    apply algebraMap_int_injective K w P
    rw [map_zero]
    have : (algebraMap OP KP (algebraMap Zw OP r)) = 0 := h0
    exact Subtype.val_injective (by simpa using this)
  surj := by
    intro y
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_integers K w P y
    have hπ0 : (unif w : Zw) ^ k ∈ Zw⁰ := pow_mem (mem_nonZeroDivisors_of_ne_zero (unif_ne_zero w)) k
    refine ⟨⟨⟨_, hk⟩, ⟨algebraMap Zw OP ((unif w) ^ k), _, hπ0, rfl⟩⟩, ?_⟩
    show y * (algebraMap OP KP (algebraMap Zw OP ((unif w) ^ k))) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply Zw Qw KP, map_pow, map_pow, mul_comm]
    rfl
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using Subtype.val_injective h⟩

private theorem norm_one_add_smul_sub_sub_mem {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] (c : R) (z : S) :
    Algebra.norm R (1 + c • z) - 1 - c * Algebra.trace R S z ∈ Ideal.span ({c ^ 2} : Set R) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  have : Algebra.leftMulMatrix b (1 + c • z) = 1 + c • Algebra.leftMulMatrix b z := by
    rw [map_add, map_one, map_smul]
  rw [this, Matrix.det_one_add_smul]
  refine Ideal.mem_span_singleton'.mpr
    ⟨(Matrix.det (1 + (Polynomial.X : Polynomial R) • (Algebra.leftMulMatrix b z).map Polynomial.C)).divX.divX.eval c,
      ?_⟩
  ring

private theorem norm_algebraMap_int (z : OP) : Algebra.norm Qw (z : KP) = algebraMap Zw Qw (Algebra.norm Zw z) :=
  Algebra.norm_localization Zw (Zw⁰) (Sₘ := KP) z

private theorem trace_algebraMap_int (z : OP) :
    Algebra.trace Qw KP (z : KP) = algebraMap Zw Qw (Algebra.trace Zw OP z) :=
  Algebra.trace_localization Zw (Zw⁰) (Sₘ := KP) z

private theorem main (m : ℕ) (x : KP) (hx : Valued.v x ≤ WithZero.exp (-(m : ℤ))) :
    Valued.v (Algebra.norm Qw (1 + x) - 1 - Algebra.trace Qw KP x) ≤
      WithZero.exp (-((2 * (m / w.asIdeal.ramificationIdx' P.1.asIdeal) : ℕ) : ℤ)) := by
  classical
  set e := w.asIdeal.ramificationIdx' P.1.asIdeal with he
  set k := m / e with hk
  set πK : KP := algebraMap Qw KP (unif w : Zw) with hπK
  have hπ0 : πK ≠ 0 := algebraMap_unif_ne_zero K w P

  have hz1 : Valued.v ((πK ^ k)⁻¹ * x) ≤ 1 := by
    have hke : ((k * e : ℕ) : ℤ) ≤ m := by exact_mod_cast Nat.div_mul_le_self m e
    rw [map_mul, map_inv₀, map_pow, hπK, valued_algebraMap_unif, ← WithZero.exp_nsmul, ← WithZero.exp_neg]
    calc WithZero.exp (-(k • -(e : ℤ))) * Valued.v x
        ≤ WithZero.exp (-(k • -(e : ℤ))) * WithZero.exp (-(m : ℤ)) := by gcongr
      _ ≤ 1 := by
        rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, smul_neg, neg_neg, nsmul_eq_mul]
        push_cast at hke
        linarith
  set z : OP := ⟨(πK ^ k)⁻¹ * x, (mem_adicCompletionIntegers _ _ _).mpr hz1⟩ with hz
  have hxz : πK ^ k * (z : KP) = x := by
    show πK ^ k * ((πK ^ k)⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_mul]
  have hxz' : ((unif w : Zw) : Qw) ^ k • (z : KP) = x := by
    rw [Algebra.smul_def, map_pow, ← hπK, hxz]

  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (norm_one_add_smul_sub_sub_mem ((unif w) ^ k) z)
  have h1 : (((1 + (unif w) ^ k • z : OP)) : KP) = 1 + x := by
    rw [← hxz]
    show ((1 : OP) : KP) + (((algebraMap Zw OP ((unif w) ^ k)) * z : OP) : KP) = 1 + πK ^ k * (z : KP)
    push_cast
    congr 1
  have hN : Algebra.norm Qw (1 + x) = algebraMap Zw Qw (Algebra.norm Zw (1 + (unif w) ^ k • z)) := by
    rw [← h1]; exact norm_algebraMap_int K w P _
  have hT : Algebra.trace Qw KP x = algebraMap Zw Qw ((unif w) ^ k * Algebra.trace Zw OP z) := by
    rw [map_mul, ← trace_algebraMap_int K w P z, ← hxz', LinearMap.map_smul, smul_eq_mul, map_pow]
    rfl
  have hmain : Algebra.norm Qw (1 + x) - 1 - Algebra.trace Qw KP x =
      algebraMap Zw Qw (t * ((unif w) ^ k) ^ 2) := by
    rw [hN, hT, ht, map_sub, map_sub, map_one]
  rw [hmain, map_mul, map_pow, map_pow]
  show Valued.v ((t : Qw) * (((unif w : Zw) : Qw) ^ k) ^ 2) ≤ _
  rw [map_mul, map_pow, map_pow, valued_unif, ← pow_mul, ← WithZero.exp_nsmul]
  calc Valued.v (t : Qw) * WithZero.exp ((k * 2) • (-1 : ℤ)) ≤ 1 * WithZero.exp ((k * 2) • (-1 : ℤ)) := by
        gcongr; exact t.2
    _ = WithZero.exp (-((2 * k : ℕ) : ℤ)) := by
        rw [one_mul, smul_neg, nsmul_eq_mul, mul_one]
        push_cast
        ring_nf

end LanglandsTunnell.TateLocal.NormTraceSecondOrder
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal.NormTraceSecondOrder"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell"

private theorem HB2.T2
    (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 ℚ)) (P : w.Extension (𝓞 K)) (m : ℕ)
    (x : P.1.adicCompletion K) (hx : Valued.v x ≤ WithZero.exp (-(m : ℤ))) :
    Valued.v (Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1 -
        Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x) ≤
      WithZero.exp (-((2 * (m / w.asIdeal.ramificationIdx' P.1.asIdeal) : ℕ) : ℤ)) :=
  LanglandsTunnell.TateLocal.NormTraceSecondOrder.main K w P m x hx

end T2sec
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal.NormTraceSecondOrder"

section T1sec

open NumberField.StandardAddChar

namespace T1Body

private theorem exp_pow (a : ℤ) (n : ℕ) : (WithZero.exp a) ^ n = WithZero.exp ((n : ℤ) * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, WithZero.exp_zero]
  | succ n ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

private theorem exp_neg' (a : ℤ) : WithZero.exp (-a) = (WithZero.exp a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero])

private theorem exp_zpow (a k : ℤ) : (WithZero.exp a) ^ k = WithZero.exp (k * a) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, exp_pow]
  · rw [zpow_neg, zpow_natCast, exp_pow, ← exp_neg']; congr 1; ring

private theorem exp_succ_le_of_not_le {a : WithZero (Multiplicative ℤ)} {n : ℤ} (h : ¬ a ≤ WithZero.exp n) :
    WithZero.exp (n + 1) ≤ a := by
  have ha : a ≠ 0 := by rintro rfl; exact h zero_le'
  rw [← WithZero.exp_log ha] at h ⊢
  rw [WithZero.exp_le_exp] at h ⊢
  omega

section Level

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem level_facts :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v)) → psiLocal K v x = 1) ∧
      ∃ x : v.adicCompletion K,
        Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v) + 1) ∧ psiLocal K v x ≠ 1 :=
  forall_eq_one_and_exists_ne_one_of_addCharLevel K v (psiLocal K v)
    ⟨0, fun x hx => psiLocal_eq_one_of_mem_integers K v x (by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero]
      exact hx)⟩
    (psiLocal_ne_one K v)

private theorem valued_le_iff_forall_psi (y : v.adicCompletion K) (n : ℤ) :
    Valued.v y ≤ WithZero.exp (addCharLevel (psiLocal K v) - n) ↔
      ∀ z : v.adicCompletion K, Valued.v z ≤ WithZero.exp n → psiLocal K v (y * z) = 1 := by
  obtain ⟨htriv, t₀, ht₀, hψt₀⟩ := level_facts K v
  constructor
  · intro hy z hz
    apply htriv
    rw [Valuation.map_mul]
    calc Valued.v y * Valued.v z ≤ WithZero.exp (addCharLevel (psiLocal K v) - n) * WithZero.exp n :=
          mul_le_mul' hy hz
      _ = WithZero.exp (addCharLevel (psiLocal K v)) := by rw [← WithZero.exp_add]; congr 1; ring
  · intro h
    by_contra hy
    have hy' := exp_succ_le_of_not_le hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy'
      exact WithZero.exp_ne_zero (le_antisymm hy' zero_le')
    have hvy0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr hy0

    have hz : Valued.v (t₀ * y⁻¹) ≤ WithZero.exp n := by
      rw [Valuation.map_mul, map_inv₀, ← div_eq_mul_inv, div_le_iff₀ hvy0]
      calc Valued.v t₀ ≤ WithZero.exp (addCharLevel (psiLocal K v) + 1) := ht₀
        _ = WithZero.exp n * WithZero.exp (addCharLevel (psiLocal K v) - n + 1) := by
            rw [← WithZero.exp_add]; congr 1; ring
        _ ≤ WithZero.exp n * Valued.v y := mul_le_mul_right hy' _
    have := h (t₀ * y⁻¹) hz
    rw [mul_comm, inv_mul_cancel_right₀ hy0] at this
    exact hψt₀ this

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal.NormTraceSecondOrder"

section Local

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 ℚ)) (P : w.Extension (𝓞 K))

private theorem valued_algebraMap (z : w.adicCompletion ℚ) :
    Valued.v (algebraMap (w.adicCompletion ℚ) (P.1.adicCompletion K) z) =
      Valued.v z ^ w.asIdeal.ramificationIdx' P.1.asIdeal := by
  have h := P.valued_adicCompletionSemialgHom ℚ K z
  rw [P.2] at h
  exact h

private theorem trace_algebraMap_mul (z : w.adicCompletion ℚ) (x : P.1.adicCompletion K) :
    Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K)
        (algebraMap (w.adicCompletion ℚ) (P.1.adicCompletion K) z * x) =
      z * Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

private theorem valued_le_iff_forall_psi_rat (y : w.adicCompletion ℚ) (n : ℤ) :
    Valued.v y ≤ WithZero.exp (-n) ↔
      ∀ z : w.adicCompletion ℚ, Valued.v z ≤ WithZero.exp n → psiLocal ℚ w (y * z) = 1 := by
  have h := valued_le_iff_forall_psi ℚ w y n
  rwa [addCharLevel_psiLocal_rat w, zero_sub] at h

private theorem valued_trace_le (m n : ℤ)
    (hn : (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * n ≤ m + addCharLevel (psiLocal K P.1))
    (x : P.1.adicCompletion K) (hx : Valued.v x ≤ WithZero.exp (-m)) :
    Valued.v (Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x) ≤ WithZero.exp (-n) := by
  rw [valued_le_iff_forall_psi_rat]
  intro z hz
  rw [mul_comm, ← trace_algebraMap_mul, ← psiLocal_eq_psiLocal_trace ℚ K w P]
  apply (level_facts K P.1).1
  rw [Valuation.map_mul, valued_algebraMap]
  calc Valued.v z ^ w.asIdeal.ramificationIdx' P.1.asIdeal * Valued.v x
        ≤ WithZero.exp n ^ w.asIdeal.ramificationIdx' P.1.asIdeal * WithZero.exp (-m) :=
          mul_le_mul' (pow_le_pow_left' hz _) hx
    _ = WithZero.exp ((w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * n - m) := by
          rw [exp_pow, ← WithZero.exp_add, ← sub_eq_add_neg]
    _ ≤ WithZero.exp (addCharLevel (psiLocal K P.1)) := WithZero.exp_le_exp.mpr (by linarith)

private theorem exists_valued_eq (k : ℤ) : ∃ z : w.adicCompletion ℚ, z ≠ 0 ∧ Valued.v z = WithZero.exp k := by
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer ℚ w
  have hϖ' : Valued.v (ϖ : w.adicCompletion ℚ) = WithZero.exp (-1) := hϖ
  have hϖ0 : (ϖ : w.adicCompletion ℚ) ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  refine ⟨(ϖ : w.adicCompletion ℚ) ^ (-k), zpow_ne_zero _ hϖ0, ?_⟩
  rw [map_zpow₀, hϖ', exp_zpow]; try (congr 1; ring)

private theorem exists_not_valued_trace_le (m n : ℤ)
    (hn : m + addCharLevel (psiLocal K P.1) < (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * (n + 1)) :
    ∃ x : P.1.adicCompletion K, Valued.v x ≤ WithZero.exp (-m) ∧
      ¬ Valued.v (Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x) ≤ WithZero.exp (-(n + 1)) := by
  by_contra H
  push Not at H
  obtain ⟨htriv, x₁, hx₁, hψx₁⟩ := level_facts K P.1
  obtain ⟨z, hz0, hz⟩ := exists_valued_eq w (n + 1)
  set ι := algebraMap (w.adicCompletion ℚ) (P.1.adicCompletion K) with hι
  have hιz0 : ι z ≠ 0 := by rw [hι]; exact (map_ne_zero _).mpr hz0

  set x : P.1.adicCompletion K := ι z⁻¹ * x₁ with hxdef
  have hxm : Valued.v x ≤ WithZero.exp (-m) := by
    rw [hxdef, Valuation.map_mul, hι, valued_algebraMap, map_inv₀, hz, ← exp_neg', exp_pow]
    calc WithZero.exp ((w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * -(n + 1)) * Valued.v x₁
          ≤ WithZero.exp ((w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * -(n + 1)) *
              WithZero.exp (addCharLevel (psiLocal K P.1) + 1) := mul_le_mul_right hx₁ _
      _ = WithZero.exp ((w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * -(n + 1) +
              (addCharLevel (psiLocal K P.1) + 1)) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-m) := WithZero.exp_le_exp.mpr (by linarith)
  have hx1 : x₁ = ι z * x := by rw [hxdef, map_inv₀, mul_inv_cancel_left₀ hιz0]

  have htr := H x hxm
  have key : psiLocal ℚ w (Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x * z) = 1 :=
    (valued_le_iff_forall_psi_rat w _ (n + 1)).mp htr z hz.le
  apply hψx₁
  rw [hx1, psiLocal_eq_psiLocal_trace ℚ K w P, hι, trace_algebraMap_mul, mul_comm]
  exact key

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal.NormTraceSecondOrder"

end T1Body
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal.NormTraceSecondOrder"

open T1Body in
private theorem HB2.T1
    (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 ℚ)) (P : w.Extension (𝓞 K)) (m : ℤ) :
    (Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K)) ''
        {x : P.1.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} =
      {y : w.adicCompletion ℚ | Valued.v y ≤
        WithZero.exp
          (-((m + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1)) /
            (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ)))} := by
  classical
  set d : ℤ := LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1) with hd
  set e : ℕ := w.asIdeal.ramificationIdx' P.1.asIdeal with he
  have he0 : e ≠ 0 := by
    have h := IsDedekindDomain.HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 ℚ) (𝓞 K)
      (algebraMap_injective_of_field_isFractionRing (𝓞 ℚ) (𝓞 K) ℚ K) P.1
    rwa [P.2] at h
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero he0

  set n : ℤ := (m + d) / (e : ℤ) with hndef
  have hn1 : (e : ℤ) * n ≤ m + d := by
    have h := Int.mul_ediv_add_emod (m + d) (e : ℤ)
    have h2 := Int.emod_nonneg (m + d) heZ.ne'
    linarith
  have hn2 : m + d < (e : ℤ) * (n + 1) := by
    have h := Int.mul_ediv_add_emod (m + d) (e : ℤ)
    have h2 := Int.emod_lt_of_pos (m + d) heZ
    linarith
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact valued_trace_le K w P m n hn1 x hx
  · intro hy
    change Valued.v y ≤ WithZero.exp (-n) at hy

    obtain ⟨x₀, hx₀, hnot⟩ := exists_not_valued_trace_le K w P m n hn2
    set t := Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x₀ with htdef
    have ht1 : Valued.v t ≤ WithZero.exp (-n) := valued_trace_le K w P m n hn1 x₀ hx₀
    have ht2 : WithZero.exp (-n) ≤ Valued.v t := by
      have h := exp_succ_le_of_not_le hnot
      rwa [show -(n + 1) + 1 = -n by ring] at h
    have ht : Valued.v t = WithZero.exp (-n) := le_antisymm ht1 ht2
    have ht0 : t ≠ 0 := by
      intro h; rw [h, map_zero] at ht; exact WithZero.exp_ne_zero ht.symm

    refine ⟨algebraMap (w.adicCompletion ℚ) (P.1.adicCompletion K) (y * t⁻¹) * x₀, ?_, ?_⟩
    · show Valued.v (algebraMap (w.adicCompletion ℚ) (P.1.adicCompletion K) (y * t⁻¹) * x₀) ≤ WithZero.exp (-m)
      have hz : Valued.v (y * t⁻¹) ≤ 1 := by
        rw [Valuation.map_mul, map_inv₀, ht, ← exp_neg', neg_neg]
        calc Valued.v y * WithZero.exp n ≤ WithZero.exp (-n) * WithZero.exp n := mul_le_mul_left hy _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      rw [Valuation.map_mul, valued_algebraMap]
      calc Valued.v (y * t⁻¹) ^ w.asIdeal.ramificationIdx' P.1.asIdeal * Valued.v x₀
            ≤ 1 ^ w.asIdeal.ramificationIdx' P.1.asIdeal * WithZero.exp (-m) :=
              mul_le_mul' (pow_le_pow_left' hz _) hx₀
        _ = WithZero.exp (-m) := by rw [one_pow, one_mul]
    · rw [trace_algebraMap_mul, ← htdef, inv_mul_cancel_right₀ ht0]

end T1sec
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal.NormTraceSecondOrder"

namespace TLocBody

private theorem arith (e c D M : ℕ) (he : 1 ≤ e) (hc : 2 * D + 2 ≤ c) (hM : e * c ≤ M + D) :
    c ≤ 2 * ((M - 1) / e) ∧ c ≤ 2 * (M / e) ∧ 2 ≤ M := by
  have hM2 : 2 ≤ M := by nlinarith
  have key : c - D - 1 ≤ (M - 1) / e := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : D + 1 ≤ c := by omega
    zify [(by omega : D ≤ c), (by omega : 1 ≤ c - D), (by omega : 1 ≤ M)]
    have hD : (0 : ℤ) ≤ (D : ℤ) + 1 := by positivity
    have he' : (0 : ℤ) ≤ (e : ℤ) - 1 := by
      have : (1 : ℤ) ≤ e := by exact_mod_cast he
      linarith
    have hM' : (e : ℤ) * c ≤ (M : ℤ) + D := by exact_mod_cast hM
    nlinarith [mul_nonneg he' hD]
  have key2 : (M - 1) / e ≤ M / e := Nat.div_le_div_right (Nat.sub_le M 1)
  refine ⟨by omega, by omega, hM2⟩

end TLocBody
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq.LanglandsTunnell.TateLocal.NormTraceSecondOrder"

open TLocBody in
private theorem HB2.TLoc
    (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 ℚ)) (P : w.Extension (𝓞 K)) :
    ∃ c₀ : ℕ, ∀ (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), c₀ ≤ c → HasConductorExponentAt ℚ w χ c →
      ∀ a : ℕ, HasConductorExponentAt K P.1 (χ.comp (Units.map (Algebra.norm (w.adicCompletion ℚ)))) a →
        (a : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1) =
          (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * c := by
  classical

  have hT1 := HB2.T1 K w P
  have hT2 := HB2.T2 K w P
  set d : ℤ := LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1) with hd
  set e : ℕ := w.asIdeal.ramificationIdx' P.1.asIdeal with he

  have he0 : e ≠ 0 := by
    have h := IsDedekindDomain.HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 ℚ) (𝓞 K)
      (algebraMap_injective_of_field_isFractionRing (𝓞 ℚ) (𝓞 K) ℚ K) P.1
    rwa [P.2] at h
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he1
  refine ⟨2 * d.natAbs + 2, ?_⟩
  intro χ c hc hχ a ha

  have hDd : -|d| ≤ d ∧ d ≤ |d| := ⟨neg_abs_le d, le_abs_self d⟩
  have hec : (c : ℤ) ≤ (e : ℤ) * c := le_mul_of_one_le_left (by positivity) (by exact_mod_cast he1)
  have hMpos : (0 : ℤ) ≤ (e : ℤ) * c - d := by
    have : (2 * d.natAbs + 2 : ℕ) ≤ (c : ℤ) := by exact_mod_cast hc
    push_cast at this
    linarith [hDd.2]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = (e : ℤ) * c - d := ⟨((e : ℤ) * c - d).toNat, Int.toNat_of_nonneg hMpos⟩
  have hMD : e * c ≤ M + d.natAbs := by
    have h1 : ((e * c : ℕ) : ℤ) ≤ ((M + d.natAbs : ℕ) : ℤ) := by push_cast; linarith [hDd.1]
    exact_mod_cast h1
  obtain ⟨hA3, hA2, hM2⟩ := arith e c d.natAbs M he1 hc hMD
  have hc1 : 1 ≤ c := by omega

  have hexpc : WithZero.exp (-(c : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)

  suffices hmain : HasConductorExponentAt K P.1 (χ.comp (Units.map (Algebra.norm (w.adicCompletion ℚ)))) M by
    have haM : a = M := hasConductorExponentAt_unique K P.1 ha hmain
    rw [haM, hM]; ring
  constructor
  ·
    intro u hu
    rw [MonoidHom.comp_apply]
    obtain ⟨hu1, hu2⟩ := (mem_higherUnitsAt_iff K P.1).mp hu
    have hx : Valued.v ((u : P.1.adicCompletion K) - 1) ≤ WithZero.exp (-(M : ℤ)) := hu2.resolve_left (by omega)
    set x : P.1.adicCompletion K := (u : P.1.adicCompletion K) - 1 with hxdef
    have hux : (u : P.1.adicCompletion K) = 1 + x := by rw [hxdef]; ring

    have htr : Valued.v (Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x) ≤ WithZero.exp (-(c : ℤ)) := by
      have hmem : Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x ∈
          (Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K)) ''
            {x : P.1.adicCompletion K | Valued.v x ≤ WithZero.exp (-(M : ℤ))} := ⟨x, hx, rfl⟩
      rw [hT1 (M : ℤ)] at hmem
      refine (show Valued.v _ ≤ _ from hmem).trans (WithZero.exp_le_exp.mpr (neg_le_neg ?_))
      rw [Int.le_ediv_iff_mul_le heZ, hM]
      linarith

    have hR : Valued.v (Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1 -
        Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x) ≤ WithZero.exp (-(c : ℤ)) :=
      (hT2 M x hx).trans (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hA2)))
    have hN1 : Valued.v (Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      have hsplit : Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1 =
          Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x +
            (Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1 -
              Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x) := by ring
      rw [hsplit]
      exact Valuation.map_add_le _ htr hR
    have hNval : Valued.v (Algebra.norm (w.adicCompletion ℚ) (1 + x)) = 1 := by
      have hsplit : Algebra.norm (w.adicCompletion ℚ) (1 + x) =
          1 + (Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1) := by ring
      rw [hsplit]
      exact Valued.v.map_one_add_of_lt (hN1.trans_lt hexpc)
    have hmem : Units.map (↑(Algebra.norm (w.adicCompletion ℚ) :
        P.1.adicCompletion K →* w.adicCompletion ℚ)) u ∈ higherUnitsAt ℚ w c := by
      refine (mem_higherUnitsAt_iff ℚ w).mpr ⟨?_, Or.inr ?_⟩
      · rw [Units.coe_map, hux]; exact hNval
      · rw [Units.coe_map, hux]; exact hN1
    exact hχ.1 _ hmem
  ·
    intro m hm

    obtain ⟨t, ht, hχt⟩ := hχ.2 (c - 1) (by omega)
    obtain ⟨ht1, ht2⟩ := (mem_higherUnitsAt_iff ℚ w).mp ht

    have hc2 : 2 ≤ c := by omega
    have hy : Valued.v ((t : w.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((c : ℤ) - 1)) := by
      have h := ht2.resolve_left (by omega)
      have hcast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
      rwa [hcast] at h

    have hX : ((M : ℤ) - 1 + d) / (e : ℤ) ≤ (c : ℤ) - 1 := by
      have hlt : ((M : ℤ) - 1 + d) / (e : ℤ) < c := by
        rw [Int.ediv_lt_iff_lt_mul heZ, hM]; linarith
      omega
    have hyR : ((t : w.adicCompletion ℚ) - 1) ∈
        {y : w.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-((((M : ℤ) - 1) + d) / (e : ℤ)))} :=
      hy.trans (WithZero.exp_le_exp.mpr (neg_le_neg hX))
    rw [← hT1 ((M : ℤ) - 1)] at hyR
    obtain ⟨x, hx, hxy⟩ := hyR
    have hx' : Valued.v x ≤ WithZero.exp (-((M - 1 : ℕ) : ℤ)) := by
      have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
      rw [hcast]; exact hx
    have hx1 : Valued.v x < 1 := by
      refine hx'.trans_lt ?_
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)
    have h1x : Valued.v (1 + x) = 1 := Valued.v.map_one_add_of_lt hx1
    have h1x0 : (1 + x : P.1.adicCompletion K) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1x; exact zero_ne_one h1x

    let u : (P.1.adicCompletion K)ˣ := Units.mk0 (1 + x) h1x0
    have hu : u ∈ higherUnitsAt K P.1 m := by
      refine (mem_higherUnitsAt_iff K P.1).mpr ⟨?_, Or.inr ?_⟩
      · show Valued.v (1 + x) = 1
        exact h1x
      · show Valued.v ((1 + x) - 1) ≤ _
        rw [add_sub_cancel_left]
        exact hx'.trans (WithZero.exp_le_exp.mpr (by omega))
    refine ⟨u, hu, ?_⟩
    rw [MonoidHom.comp_apply]

    have hR : Valued.v (Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1 -
        Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x) ≤ WithZero.exp (-(c : ℤ)) :=
      (hT2 (M - 1) x hx').trans (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hA3)))
    set R : w.adicCompletion ℚ := Algebra.norm (w.adicCompletion ℚ) (1 + x) - 1 -
        Algebra.trace (w.adicCompletion ℚ) (P.1.adicCompletion K) x with hRdef
    have hNu : ((Units.map (↑(Algebra.norm (w.adicCompletion ℚ) :
        P.1.adicCompletion K →* w.adicCompletion ℚ)) u : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) =
          (t : w.adicCompletion ℚ) + R := by
      rw [Units.coe_map]
      show Algebra.norm (w.adicCompletion ℚ) (1 + x) = (t : w.adicCompletion ℚ) + R
      rw [hRdef, hxy]; ring

    set Nu : (w.adicCompletion ℚ)ˣ := Units.map (↑(Algebra.norm (w.adicCompletion ℚ) :
        P.1.adicCompletion K →* w.adicCompletion ℚ)) u with hNudef
    have ht0 : (t : w.adicCompletion ℚ) ≠ 0 := t.ne_zero
    have hs1 : Valued.v (((Nu * t⁻¹ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) - 1) ≤
        WithZero.exp (-(c : ℤ)) := by
      have hval : ((Nu * t⁻¹ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) - 1 =
          R * (t : w.adicCompletion ℚ)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, hNu]
        field_simp
        ring
      rw [hval, Valuation.map_mul, map_inv₀, ht1, inv_one, mul_one]
      exact hR
    have hsval : Valued.v (((Nu * t⁻¹ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ)) = 1 := by
      have hsplit : (((Nu * t⁻¹ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ)) =
          1 + ((((Nu * t⁻¹ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ)) - 1) := by ring
      rw [hsplit]
      exact Valued.v.map_one_add_of_lt (hs1.trans_lt hexpc)
    have hsmem : Nu * t⁻¹ ∈ higherUnitsAt ℚ w c :=
      (mem_higherUnitsAt_iff ℚ w).mpr ⟨hsval, Or.inr hs1⟩
    have hχs : χ (Nu * t⁻¹) = 1 := hχ.1 _ hsmem
    have hfac : Nu = (Nu * t⁻¹) * t := by group
    rw [hfac, map_mul, hχs, one_mul]
    exact hχt

theorem solution
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c₀ : ℕ, ∀ (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ), c₀ ≤ c → HasConductorExponentAt ℚ w χ c →
      ∀ a : w.Extension (𝓞 K) → ℕ,
        (∀ P : w.Extension (𝓞 K),
          HasConductorExponentAt K P.1 (χ.comp (Units.map (Algebra.norm (w.adicCompletion ℚ)))) (a P)) →
        ∑ᶠ P : w.Extension (𝓞 K), (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ) *
            ((a P : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1)) =
          3 * c := by
  classical
  letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) w
  choose c₀ hc₀ using fun P : w.Extension (𝓞 K) =>
    HB2.TLoc K w P
  refine ⟨Finset.univ.sup c₀, ?_⟩
  intro χ c hc hχ a ha
  have key : ∀ P : w.Extension (𝓞 K),
      ((a P : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1)) =
        (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * c := fun P =>
    hc₀ P χ c ((Finset.le_sup (Finset.mem_univ P)).trans hc) hχ (a P) (ha P)
  have hsum : (∑ P : w.Extension (𝓞 K),
      (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ)) = 3 := by
    have h := Ideal.sum_ramification_inertia_extensions (𝓞 ℚ) ℚ K (𝓞 K) w
    rw [hdeg] at h
    exact_mod_cast h
  rw [finsum_eq_sum_of_fintype]
  calc ∑ P : w.Extension (𝓞 K), (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ) *
          ((a P : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K P.1))
      = ∑ P : w.Extension (𝓞 K), (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ) *
          ((w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * c) := Finset.sum_congr rfl fun P _ => by rw [key P]
    _ = (c : ℤ) * ∑ P : w.Extension (𝓞 K),
          (w.asIdeal.ramificationIdx' P.1.asIdeal : ℤ) * (w.asIdeal.inertiaDeg' P.1.asIdeal : ℤ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun P _ => by ring
    _ = 3 * c := by rw [hsum]; ring

end S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_forall_finsum_inertiaDeg_mul_conductorExponent_add_addCharLevel_eq (solution)
