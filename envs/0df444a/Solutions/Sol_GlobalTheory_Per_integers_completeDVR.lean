-- Prove2me | solution 1 for GlobalTheory.Per.integers_completeDVR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:14:45.613051+00:00
-- url     : https://prove2.me/submissions/5687db58-f777-42b4-a538-a70178a78496

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X


section
namespace GlobalTheory.Per
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
private theorem isIntegral_iff_spectralNorm_le_one' {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] (x : K) :
    IsIntegral ℤ_[p] x ↔ spectralNorm ℚ_[p] K x ≤ 1 := by
  have hx : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hlift : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨(minpoly ℚ_[p] x).coeff n, h n⟩, rfl⟩
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hx)
    refine ⟨g, hgm, ?_⟩
    have h0 := minpoly.aeval ℚ_[p] x
    rw [← hg, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def] at h0
    exact h0
private theorem spectralNorm_mul_zpadic {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] (x y : K) :
    spectralNorm ℚ_[p] K (x * y) = spectralNorm ℚ_[p] K x * spectralNorm ℚ_[p] K y := by
  simpa only [spectralMulAlgNorm_def] using map_mul (spectralMulAlgNorm ℚ_[p] K) x y
private theorem isUnit_iff_spectralNorm_eq_one {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (b : integralClosure ℤ_[p] K) : IsUnit b ↔ spectralNorm ℚ_[p] K (b : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : integralClosure ℤ_[p] K) : K) * ((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : K) = 1 := by
      have := congrArg (fun z : integralClosure ℤ_[p] K => (z : K)) u.mul_inv
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_one] using this
    have h2 := congrArg (spectralNorm ℚ_[p] K) h1
    rw [spectralNorm_mul_zpadic, spectralNorm_one] at h2
    have ha := (isIntegral_iff_spectralNorm_le_one' _).mp (u : integralClosure ℤ_[p] K).2
    have hb := (isIntegral_iff_spectralNorm_le_one' _).mp ((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K).2
    have ha0 := spectralNorm_nonneg (K := ℚ_[p]) ((u : integralClosure ℤ_[p] K) : K)
    have hb0 := spectralNorm_nonneg (K := ℚ_[p])
      (((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K) : K)
    nlinarith
  · intro h
    have hb0 : (b : K) ≠ 0 := by
      intro h0
      rw [h0, spectralNorm_zero] at h
      exact zero_ne_one h
    have hinv : IsIntegral ℤ_[p] (b : K)⁻¹ := by
      rw [isIntegral_iff_spectralNorm_le_one']
      have h2 := spectralNorm_mul_zpadic (p := p) (b : K) (b : K)⁻¹
      rw [mul_inv_cancel₀ hb0, spectralNorm_one, h, one_mul] at h2
      exact h2.symm.le
    exact isUnit_iff_exists_inv.mpr ⟨⟨(b : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb0)⟩
private theorem isLocalRing_integralClosure_zpadic {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] :
    IsLocalRing (integralClosure ℤ_[p] K) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb hab
  have hlt : ∀ c : integralClosure ℤ_[p] K, ¬IsUnit c → spectralNorm ℚ_[p] K (c : K) < 1 :=
    fun c hc => lt_of_le_of_ne ((isIntegral_iff_spectralNorm_le_one' _).mp c.2) (fun h => hc ((isUnit_iff_spectralNorm_eq_one c).mpr h))
  have h1 := hlt a ha
  have h2 := hlt b hb
  have h3 := (isUnit_iff_spectralNorm_eq_one (a + b)).mp hab
  have h4 := isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := K) (a : K) (b : K)
  have h5 : ((a + b : integralClosure ℤ_[p] K) : K) = (a : K) + (b : K) := rfl
  rw [h5] at h3
  rw [h3] at h4
  exact absurd h4 (not_le.mpr (max_lt h1 h2))
private theorem isPrecomplete_maximalIdeal_of_free_finite_zpadic {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    [Module ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[p]) M := by
  classical
  set b := Module.Free.chooseBasis ℤ_[p] M
  have key : ∀ (n : ℕ) (x : M), x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] M) ↔
      ∀ i, b.equivFun x i ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
    intro n x
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr m _ i
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy i
        simp only [map_add, Pi.add_apply]
        exact add_mem (hx i) (hy i)
    · intro h
      rw [← b.sum_equivFun x]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top)
  have key1 : ∀ (n : ℕ) (y : ℤ_[p]),
      y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] ℤ_[p]) ↔
        y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
    intro n y
    change y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Ideal ℤ_[p]) ↔ _
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [isPrecomplete_iff]
  intro f hf
  have hc : ∀ i, ∃ L : ℤ_[p], ∀ n, b.equivFun (f n) i ≡ L
      [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ n • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i
    refine IsPrecomplete.prec inferInstance ?_
    intro m n hmn
    rw [SModEq.sub_mem, key1]
    have := (key m _).mp (SModEq.sub_mem.mp (hf hmn)) i
    simpa only [map_sub, Pi.sub_apply] using this
  choose L hL using hc
  refine ⟨b.equivFun.symm L, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  have := (key1 n _).mp (SModEq.sub_mem.mp (hL i n))
  simpa only [map_sub, Pi.sub_apply, LinearEquiv.apply_symm_apply] using this
private theorem isPrecomplete_of_isPrecomplete_pow {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e)
    (h : IsPrecomplete (I ^ e) R) : IsPrecomplete I R := by
  rw [isPrecomplete_iff]
  intro f hf
  obtain ⟨L, hL⟩ := h.prec (f := fun k => f (e * k)) (fun {m n} hmn => by
    rw [← pow_mul]
    exact hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := by nlinarith
  have h1 : f n ≡ f (e * n) [SMOD (I ^ n • ⊤ : Submodule R R)] := hf hn
  have h2 := hL n
  rw [← pow_mul] at h2
  exact h1.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)))
private theorem isAdicComplete_maximalIdeal_of_free_finite_zpadic {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra ℤ_[p] B] [Module.Free ℤ_[p] B] [Module.Finite ℤ_[p] B]
    (hp0 : (p : B) ≠ 0) (hpu : ¬IsUnit (p : B)) :
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  have hJ : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B) = Ideal.span {(p : B)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hprecJ : IsPrecomplete ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr isPrecomplete_maximalIdeal_of_free_finite_zpadic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : B)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at he
  have he0 : 0 < e := Nat.pos_of_ne_zero (fun h => by
    rw [h, pow_zero, Ideal.one_eq_top] at he
    exact hpu (Ideal.span_singleton_eq_top.mp he))
  have hprec : IsPrecomplete (IsLocalRing.maximalIdeal B ^ e) B := by
    rw [← he, ← hJ]
    exact hprecJ
  exact { toIsHausdorff := inferInstance,
          toIsPrecomplete := isPrecomplete_of_isPrecomplete_pow _ e he0 hprec }
end GlobalTheory.Per
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.Per
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.Per
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime], ∀ LL : FinExt l,
    ∃ _ : IsDiscreteValuationRing ↥(OL LL),
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ((l : ℕ) : ↥(OL LL)) ≠ 0 ∧
      ¬ IsUnit ((l : ℕ) : ↥(OL LL)) ∧ Module.Free ℤ_[l] ↥(OL LL) ∧ Module.Finite ℤ_[l] ↥(OL LL) ∧
      IsFractionRing ↥(OL LL) ↥LL.1 := by
  intro l _ LL
  unfold OL
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : Algebra.IsAlgebraic ℚ_[l] ↥LL.1 := Algebra.IsAlgebraic.of_finite ℚ_[l] ↥LL.1
  have hloc : IsLocalRing (integralClosure ℤ_[l] ↥LL.1) := isLocalRing_integralClosure_zpadic
  have hN : spectralNorm ℚ_[l] ↥LL.1 (((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) =
      (l : ℝ)⁻¹ := by
    have : (((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l]) := by
      simp
    rw [this, spectralNorm_extends, Padic.norm_p]
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hpu : ¬IsUnit ((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) := by
    intro h
    have := (isUnit_iff_spectralNorm_eq_one _).mp h
    rw [hN] at this
    exact absurd this hl1.ne
  have hp0 : ((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) ≠ 0 := by
    intro h
    rw [h] at hN
    simp only [ZeroMemClass.coe_zero, spectralNorm_zero] at hN
    exact hl0 hN.symm
  have hnf : ¬IsField (integralClosure ℤ_[l] ↥LL.1) := by
    intro h
    obtain ⟨c, hc⟩ := h.mul_inv_cancel hp0
    exact hpu (isUnit_iff_exists_inv.mpr ⟨c, hc⟩)
  have hded : IsDedekindDomain (integralClosure ℤ_[l] ↥LL.1) := inferInstance
  have hdvr : IsDiscreteValuationRing (integralClosure ℤ_[l] ↥LL.1) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) := inferInstance
  have htf : Module.IsTorsionFree ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    have hne : algebraMap ℤ_[l] ↥LL.1 r ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hr0)
    have h : ((r • x : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) =
        ((r • y : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) := congrArg Subtype.val hxy
    change r • (x : ↥LL.1) = r • (y : ↥LL.1) at h
    rw [Algebra.smul_def, Algebra.smul_def] at h
    exact Subtype.ext (mul_left_cancel₀ hne h)
  have hfree : Module.Free ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) :=
    Module.free_of_finite_type_torsion_free'
  exact ⟨hdvr, isAdicComplete_maximalIdeal_of_free_finite_zpadic hp0 hpu, hp0, hpu, hfree, hfin,
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1⟩
end GlobalTheory.Per
