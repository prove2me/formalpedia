-- Prove2me | solution 1 for HeckeCharacter.exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0c92772f-b155-5440-97ce-b8d95a220dee

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain HeckeCharacter NumberField.AdelicLevel NumberField.TateGlobal

open scoped Topology

noncomputable section

namespace R4Adm

theorem half_lt_re_of_norm_sub_one_lt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1) : 1 / 2 < w.re := by
  have h1 : w.re * w.re + w.im * w.im = 1 := by
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this
    linarith
  have h2 : ‖w - 1‖ ^ 2 = 2 - 2 * w.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  have h3 : ‖w - 1‖ ^ 2 < 1 := by
    have h0 : 0 ≤ ‖w - 1‖ := norm_nonneg _
    nlinarith
  linarith

theorem eq_one_of_norm_eq_one_of_forall_norm_pow_sub_one_lt {z : ℂ} (hz : ‖z‖ = 1)
    (h : ∀ m : ℕ, ‖z ^ m - 1‖ < 1) : z = 1 := by
  by_contra hne
  have hre1 : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    linarith
  have hzre : z.re < 1 := by
    have hle : z.re ≤ 1 := by
      have := Complex.abs_re_le_norm z; rw [hz] at this; exact (abs_le.mp this).2
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have him : z.im = 0 := by nlinarith
      exact hne (Complex.ext (by simp [heq]) (by simp [him]))
  set d₀ : ℝ := 1 - z.re with hd₀
  have hd₀pos : 0 < d₀ := by rw [hd₀]; linarith

  have claim : ∀ k : ℕ, 3 ^ k * d₀ ≤ 1 - (z ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp [hd₀]
    | succ k ih =>
      set w : ℂ := z ^ (2 ^ k) with hwdef
      have hw : ‖w‖ = 1 := by rw [hwdef, norm_pow, hz, one_pow]
      have hwre : 1 / 2 < w.re := half_lt_re_of_norm_sub_one_lt hw (h _)
      have hw1 : w.re * w.re + w.im * w.im = 1 := by
        have := Complex.sq_norm w
        rw [hw, Complex.normSq_apply] at this
        linarith
      have hwle : w.re ≤ 1 := by
        have := Complex.abs_re_le_norm w; rw [hw] at this; exact (abs_le.mp this).2
      have hpow : z ^ (2 ^ (k + 1)) = w ^ 2 := by
        rw [hwdef, ← pow_mul, pow_succ]
      have hre2 : (w ^ 2).re = 2 * (w.re * w.re) - 1 := by
        rw [sq, Complex.mul_re]; nlinarith
      rw [hpow, hre2]
      have h3 : 3 * (1 - w.re) ≤ 1 - (2 * (w.re * w.re) - 1) := by nlinarith
      calc (3 : ℝ) ^ (k + 1) * d₀ = 3 * (3 ^ k * d₀) := by ring
        _ ≤ 3 * (1 - w.re) := by linarith
        _ ≤ 1 - (2 * (w.re * w.re) - 1) := h3
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / d₀)
  have hk3 : (k : ℝ) ≤ (3 : ℝ) ^ k := by
    exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3) (n := k)).le
  have hbig : 1 < 3 ^ k * d₀ := by
    rw [div_lt_iff₀ hd₀pos] at hk
    nlinarith
  have hw : ‖z ^ (2 ^ k)‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hwre := half_lt_re_of_norm_sub_one_lt hw (h _)
  linarith [claim k]

variable (K : Type) [Field K] [NumberField K]

def finUnit : (FiniteAdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (finIncl (𝓞 K) K)

theorem continuous_finIncl : Continuous (finIncl (𝓞 K) K) := by
  unfold finIncl
  exact Continuous.prodMk continuous_const continuous_id

theorem continuous_finUnit : Continuous (finUnit K) :=
  Continuous.units_map _ (continuous_finIncl K)

def sndUnit : (AdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

theorem finUnit_sndUnit {u : (AdeleRing (𝓞 K) K)ˣ} (hu : (u : AdeleRing (𝓞 K) K).1 = 1) :
    finUnit K (sndUnit K u) = u := by
  refine Units.ext (Prod.ext ?_ rfl)
  show (1 : InfiniteAdeleRing K) = (u : AdeleRing (𝓞 K) K).1
  exact hu.symm

theorem sndUnit_val (u : (AdeleRing (𝓞 K) K)ˣ) :
    ((sndUnit K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) = (u : AdeleRing (𝓞 K) K).2 :=
  rfl

def unitAt (v : HeightOneSpectrum (𝓞 K)) : (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (finAdeleEval (𝓞 K) K v).toMonoidHom

theorem coe_unitAt (v : HeightOneSpectrum (𝓞 K)) (y : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((unitAt K v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (y : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

theorem localChar_eq (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : localChar χ v t = χ (finUnit K (localUnit (𝓞 K) K v t)) := rfl

variable {K}

theorem fad_units_inv_apply (X : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((X⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) =
      (((X : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)⁻¹ := by
  have h : ((X : FiniteAdeleRing (𝓞 K) K) v) * (((X⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v) = 1 :=
    congrArg (fun a : FiniteAdeleRing (𝓞 K) K => a v) X.mul_inv
  exact eq_inv_of_mul_eq_one_right h

theorem fad_units_pow_apply (X : (FiniteAdeleRing (𝓞 K) K)ˣ) (m : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (((X ^ m : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) =
      (((X : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) ^ m := by
  rw [Units.val_pow_eq_pow_val, ← finAdeleEval_apply (𝓞 K) K v, map_pow, finAdeleEval_apply]

theorem valued_ne_zero_of_eq_one {v : HeightOneSpectrum (𝓞 K)} {a : v.adicCompletion K}
    (ha : Valued.v a = 1) : a ≠ 0 := fun h => by
  rw [h, map_zero] at ha; exact zero_ne_one ha

theorem valued_inv_sub_one {v : HeightOneSpectrum (𝓞 K)} {a : v.adicCompletion K}
    (ha : Valued.v a = 1) : Valued.v (a⁻¹ - 1) = Valued.v (a - 1) := by
  have ha0 : a ≠ 0 := valued_ne_zero_of_eq_one ha
  have : a⁻¹ - 1 = a⁻¹ * (1 - a) := by field_simp
  rw [this, map_mul, map_inv₀, ha, inv_one, one_mul, Valuation.map_sub_swap]

theorem valued_pow_sub_one_le {v : HeightOneSpectrum (𝓞 K)} {a : v.adicCompletion K}
    (ha : Valued.v a = 1) {g : WithZero (Multiplicative ℤ)} (h : Valued.v (a - 1) ≤ g) (m : ℕ) :
    Valued.v (a ^ m - 1) ≤ g := by
  induction m with
  | zero => simp
  | succ m ih =>
    have heq : a ^ (m + 1) - 1 = a * (a ^ m - 1) + (a - 1) := by ring
    rw [heq]
    refine Valuation.map_add_le _ ?_ h
    rw [map_mul, ha, one_mul]
    exact ih

theorem valued_eq_one_of_mem_of_inv_mem {v : HeightOneSpectrum (𝓞 K)} (u : (v.adicCompletion K)ˣ)
    (hu : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (hu' : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    Valued.v (u : v.adicCompletion K) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hu hu'
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hu'
  have h0 : Valued.v (u : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  have h1 : 1 ≤ Valued.v (u : v.adicCompletion K) := by
    rwa [inv_le_one₀ (zero_lt_iff.mpr h0)] at hu'
  exact le_antisymm hu h1

theorem mem_integers_of_valued_eq_one {v : HeightOneSpectrum (𝓞 K)} {a : v.adicCompletion K}
    (ha : Valued.v a = 1) : a ∈ v.adicCompletionIntegers K :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ha.le

theorem inv_mem_integers_of_valued_eq_one {v : HeightOneSpectrum (𝓞 K)} (u : (v.adicCompletion K)ˣ)
    (ha : Valued.v (u : v.adicCompletion K) = 1) :
    ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]

open scoped Classical in
theorem coe_prod_localUnit_apply (J : Finset (HeightOneSpectrum (𝓞 K)))
    (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (((∏ v ∈ J, localUnit (𝓞 K) K v (t v) : (FiniteAdeleRing (𝓞 K) K)ˣ)) : FiniteAdeleRing (𝓞 K) K) w
      = if w ∈ J then ((t w : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
  rw [Units.coe_prod, ← finAdeleEval_apply (𝓞 K) K w, map_prod]
  simp only [finAdeleEval_apply]
  by_cases hw : w ∈ J
  · rw [if_pos hw, Finset.prod_eq_single_of_mem w hw]
    · exact localUnit_apply_self (𝓞 K) K w (t w)
    · intro v _ hvw
      exact localUnit_apply_of_ne (𝓞 K) K v (t v) (Ne.symm hvw)
  · rw [if_neg hw]
    refine Finset.prod_eq_one fun v hv => ?_
    exact localUnit_apply_of_ne (𝓞 K) K v (t v) (fun h => hw (h ▸ hv))

def box (I : Finset (HeightOneSpectrum (𝓞 K))) (k : HeightOneSpectrum (𝓞 K) → ℕ) :
    Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
  {y | ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v (((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
    (v ∈ I → Valued.v (((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
      WithZero.exp (-(k v : ℤ)))}

theorem pow_mem_box {I : Finset (HeightOneSpectrum (𝓞 K))} {k : HeightOneSpectrum (𝓞 K) → ℕ}
    {y : (FiniteAdeleRing (𝓞 K) K)ˣ} (hy : y ∈ box I k) (m : ℕ) : y ^ m ∈ box I k := by
  intro v
  refine ⟨?_, fun hv => ?_⟩
  · rw [fad_units_pow_apply, map_pow, (hy v).1, one_pow]
  · rw [fad_units_pow_apply]
    exact valued_pow_sub_one_le (hy v).1 ((hy v).2 hv) m

open scoped Classical in
theorem localUnit_mem_box {I : Finset (HeightOneSpectrum (𝓞 K))} {k : HeightOneSpectrum (𝓞 K) → ℕ}
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1)
    (hcong : Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(k v : ℤ))) :
    localUnit (𝓞 K) K v u ∈ box I k := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localUnit_apply_self]
    exact ⟨hu, fun _ => hcong⟩
  · rw [localUnit_apply_of_ne (𝓞 K) K v u hw, map_one, sub_self, map_zero]
    exact ⟨rfl, fun _ => zero_le'⟩

open RestrictedProduct in
theorem exists_box_subset_of_mem_nhds_one {V : Set (FiniteAdeleRing (𝓞 K) K)}
    (hV : V ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ (I : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ x : FiniteAdeleRing (𝓞 K) K, (∀ v, x v ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ I, Valued.v (x v - 1) ≤ WithZero.exp (-(n v : ℤ))) → x ∈ V := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    fun v => Valued.isOpen_valuationSubring _
  have key := nhds_eq_map_structureMap hAopen
    (fun v : HeightOneSpectrum (𝓞 K) => (⟨1, (v.adicCompletionIntegers K).one_mem⟩ :
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))))
  have hV' : V ∈ Filter.map (structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite)
      (𝓝 (fun v : HeightOneSpectrum (𝓞 K) => (⟨1, (v.adicCompletionIntegers K).one_mem⟩ :
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))))) := by
    rw [← key]
    exact hV
  have hV'' : (structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite) ⁻¹' V ∈
      (𝓝 (fun v : HeightOneSpectrum (𝓞 K) => (⟨1, (v.adicCompletionIntegers K).one_mem⟩ :
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))))) := hV'
  rw [nhds_pi, Filter.mem_pi] at hV''
  obtain ⟨I, hI, t, ht, hIt⟩ := hV''
  have hball : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℕ, ∀ y : v.adicCompletionIntegers K,
      Valued.v ((y : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht v)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hu
    set δ : WithZero (Multiplicative ℤ) :=
      MonoidWithZeroHom.ValueGroup₀.embedding (γ.1 : MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass
        (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))))) with hδ
    have hδ0 : δ ≠ 0 := by
      rw [hδ]
      exact (map_ne_zero _).mpr γ.ne_zero
    refine ⟨(WithZero.log δ).natAbs + 1, fun y hy => hut (hγ ?_)⟩
    show Valued.v.restrict ((y : v.adicCompletion K) - (1 : v.adicCompletionIntegers K)) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    refine lt_of_le_of_lt hy ?_
    rw [← hδ]
    conv_rhs => rw [← WithZero.exp_log hδ0]
    rw [WithZero.exp_lt_exp]
    omega
  choose n hn using hball
  refine ⟨hI.toFinset, n, fun x hxint hxcong => ?_⟩
  have hx : x = structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite
      (fun v => ⟨x v, hxint v⟩) := RestrictedProduct.ext _ _ fun _ => rfl
  rw [hx]
  refine hIt (Set.mem_pi.mpr fun v hv => hn v _ ?_)
  exact hxcong v (hI.mem_toFinset.mpr hv)

def boxModulus (I : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    Ideal (𝓞 K) :=
  ∏ v ∈ I, v.asIdeal ^ n v

omit [NumberField K] in
theorem boxModulus_ne_bot (I : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    boxModulus I n ≠ ⊥ := by
  unfold boxModulus
  rw [Ne, ← Submodule.zero_eq_bot, Finset.prod_eq_zero_iff]
  rintro ⟨v, _, hv⟩
  exact v.ne_bot (by rw [← Submodule.zero_eq_bot]; exact eq_zero_of_pow_eq_zero hv)

theorem le_idealMultiplicity_boxModulus (I : Finset (HeightOneSpectrum (𝓞 K)))
    (n : HeightOneSpectrum (𝓞 K) → ℕ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ I) :
    n v ≤ idealMultiplicity K v (boxModulus I n) := by
  classical
  unfold idealMultiplicity
  have hdvd : v.asIdeal ^ n v ∣ boxModulus I n := Finset.dvd_prod_of_mem _ hv
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr (boxModulus_ne_bot I n))
    v.associates_irreducible, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
  exact hdvd

theorem exists_box_forall_eq_one (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχu : IsUnitaryChar (𝓞 K) K χ) :
    ∃ (I : Finset (HeightOneSpectrum (𝓞 K))) (k : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ y ∈ box I k, χ (finUnit K y) = 1 := by
  classical
  set ψ : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ := fun y => ((χ (finUnit K y) : ℂˣ) : ℂ) with hψ
  have hψc : Continuous ψ := hχc.comp (continuous_finUnit K)
  set V₀ : Set (FiniteAdeleRing (𝓞 K) K)ˣ := ψ ⁻¹' Metric.ball 1 1 with hV₀
  have hopen : IsOpen V₀ := Metric.isOpen_ball.preimage hψc
  have h1mem : (1 : (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ V₀ := by
    show ψ 1 ∈ Metric.ball 1 1
    simp [hψ]
  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp hopen
  have h1t : ((1 : FiniteAdeleRing (𝓞 K) K), (1 : (FiniteAdeleRing (𝓞 K) K)ᵐᵒᵖ)) ∈ t := by
    have h := h1mem
    rw [← hteq, Set.mem_preimage] at h
    exact h
  obtain ⟨U₁, U₂, hU₁, hU₂, h1U₁, h1U₂, hprod⟩ := isOpen_prod_iff.mp ht 1 1 h1t
  set V : Set (FiniteAdeleRing (𝓞 K) K) := U₁ ∩ MulOpposite.op ⁻¹' U₂ with hVdef
  have hV : V ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 K) K) :=
    (hU₁.inter (hU₂.preimage MulOpposite.continuous_op)).mem_nhds ⟨h1U₁, h1U₂⟩
  obtain ⟨I, k, hbox⟩ := exists_box_subset_of_mem_nhds_one hV
  refine ⟨I, k, fun y hy => ?_⟩

  have hmemV₀ : ∀ y' ∈ box I k, ‖ψ y' - 1‖ < 1 := by
    intro y' hy'
    have hyV : ((y' : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) ∈ V :=
      hbox _ (fun v => mem_integers_of_valued_eq_one (hy' v).1) (fun v hv => (hy' v).2 hv)
    have hyinvV : (((y'⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ)) : FiniteAdeleRing (𝓞 K) K) ∈ V := by
      refine hbox _ (fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_) (fun v hv => ?_)
      · rw [fad_units_inv_apply, map_inv₀, (hy' v).1, inv_one]
      · rw [fad_units_inv_apply, valued_inv_sub_one (hy' v).1]
        exact (hy' v).2 hv
    have hemb : Units.embedProduct _ y' ∈ t := hprod ⟨hyV.1, hyinvV.2⟩
    have h : y' ∈ Units.embedProduct _ ⁻¹' t := hemb
    rw [hteq] at h
    have h' : ψ y' ∈ Metric.ball (1 : ℂ) 1 := h
    rwa [Metric.mem_ball, dist_eq_norm] at h'

  have hz : ‖ψ y‖ = 1 := hχu _
  have hpow : ∀ m : ℕ, ‖ψ y ^ m - 1‖ < 1 := by
    intro m
    have h := hmemV₀ (y ^ m) (pow_mem_box hy m)
    have heq : ψ (y ^ m) = ψ y ^ m := by
      simp only [hψ, map_pow, Units.val_pow_eq_pow_val]
    rwa [heq] at h
  have h1 := eq_one_of_norm_eq_one_of_forall_norm_pow_sub_one_lt hz hpow
  exact Units.val_eq_one.mp h1

def KillsLevel (v : HeightOneSpectrum (𝓞 K)) (ρv : (v.adicCompletion K)ˣ →* ℂˣ) (n : ℕ) : Prop :=
  ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
    ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
    Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) → ρv u = 1

open scoped Classical in

def levelOf (v : HeightOneSpectrum (𝓞 K)) (ρv : (v.adicCompletion K)ˣ →* ℂˣ) : ℕ :=
  if h : ∃ n, KillsLevel v ρv n then Nat.find h else 0

open scoped Classical in
theorem killsLevel_levelOf {v : HeightOneSpectrum (𝓞 K)} {ρv : (v.adicCompletion K)ˣ →* ℂˣ}
    (h : ∃ n, KillsLevel v ρv n) : KillsLevel v ρv (levelOf v ρv) := by
  unfold levelOf
  rw [dif_pos h]
  exact Nat.find_spec h

open scoped Classical in
theorem main (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        Continuous (fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
        IsUnitaryChar (𝓞 K) K χ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v) →
        (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          localChar χ v u = ρ v u) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 := by
  set n : HeightOneSpectrum (𝓞 K) → ℕ := fun v => levelOf v (ρ v) with hndef
  refine ⟨boxModulus S n, boxModulus_ne_bot S n, ?_⟩
  intro χ hχc hχu hunr hram u hu1 hu2
  obtain ⟨I, k, hkill⟩ := exists_box_forall_eq_one χ hχc hχu

  set y : (FiniteAdeleRing (𝓞 K) K)ˣ := sndUnit K u with hydef
  have hy : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
      Valued.v (((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
        WithZero.exp (-(idealMultiplicity K v (boxModulus S n) : ℤ)) := hu2
  set t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ := fun v => unitAt K v y with htdef
  have ht : ∀ v, ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v := fun v => rfl
  have htval : ∀ v, Valued.v ((t v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := fun v => by
    rw [ht]; exact (hy v).1

  set J : Finset (HeightOneSpectrum (𝓞 K)) := I ∪ S with hJdef
  set yJ : (FiniteAdeleRing (𝓞 K) K)ˣ := ∏ v ∈ J, localUnit (𝓞 K) K v (t v) with hyJdef
  set y' : (FiniteAdeleRing (𝓞 K) K)ˣ := y * yJ⁻¹ with hy'def
  have hyJ_apply : ∀ w : HeightOneSpectrum (𝓞 K),
      ((yJ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
        if w ∈ J then ((t w : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := fun w =>
    coe_prod_localUnit_apply J t w
  have hy'_apply : ∀ w : HeightOneSpectrum (𝓞 K),
      ((y' : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
        if w ∈ J then 1 else ((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w := by
    intro w
    rw [hy'def, Units.val_mul, coe_mul_apply, fad_units_inv_apply, hyJ_apply]
    by_cases hw : w ∈ J
    · rw [if_pos hw, if_pos hw, ht]
      exact mul_inv_cancel₀ (valued_ne_zero_of_eq_one (hy w).1)
    · rw [if_neg hw, if_neg hw, inv_one, mul_one]
  have hy'box : y' ∈ box I k := by
    intro w
    rw [hy'_apply]
    by_cases hw : w ∈ J
    · rw [if_pos hw, map_one, sub_self, map_zero]
      exact ⟨rfl, fun _ => zero_le'⟩
    · rw [if_neg hw]
      refine ⟨(hy w).1, fun hwI => absurd (Finset.mem_union_left S hwI) hw⟩
  have hsplit : y = y' * yJ := by rw [hy'def, inv_mul_cancel_right]

  have hkills : ∀ v ∈ S, KillsLevel v (ρ v) (n v) := by
    intro v hv
    refine killsLevel_levelOf ⟨k v, fun u' hu' hu'' hcong => ?_⟩
    have hval : Valued.v (u' : v.adicCompletion K) = 1 := valued_eq_one_of_mem_of_inv_mem u' hu' hu''
    have h1 : χ (finUnit K (localUnit (𝓞 K) K v u')) = 1 :=
      hkill _ (localUnit_mem_box v u' hval hcong)
    rw [← hram v hv u' hu' hu'', localChar_eq]
    exact h1

  have hfactor : ∀ v ∈ J, χ (finUnit K (localUnit (𝓞 K) K v (t v))) = 1 := by
    intro v hvJ
    rw [← localChar_eq]
    by_cases hvS : v ∈ S
    · rw [hram v hvS (t v) (mem_integers_of_valued_eq_one (htval v))
        (inv_mem_integers_of_valued_eq_one (t v) (htval v))]
      refine hkills v hvS (t v) (mem_integers_of_valued_eq_one (htval v))
        (inv_mem_integers_of_valued_eq_one (t v) (htval v)) ?_
      rw [ht]
      exact (hy v).2.trans (WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr
        (le_idealMultiplicity_boxModulus S n hvS))))
    · exact hunr v hvS (t v) (mem_integers_of_valued_eq_one (htval v))
        (inv_mem_integers_of_valued_eq_one (t v) (htval v))
  have hyJ1 : χ (finUnit K yJ) = 1 := by
    rw [hyJdef, map_prod, map_prod]
    exact Finset.prod_eq_one hfactor

  rw [← finUnit_sndUnit K hu1]
  show χ (finUnit K y) = 1
  rw [hsplit, map_mul, map_mul, hkill y' hy'box, hyJ1, one_mul]

end R4Adm

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        Continuous (fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
        IsUnitaryChar (𝓞 K) K χ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v) →
        (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          localChar χ v u = ρ v u) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 :=
  R4Adm.main K S ρ

end S_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
end P2MW
export P2MW.S_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq (solution)
