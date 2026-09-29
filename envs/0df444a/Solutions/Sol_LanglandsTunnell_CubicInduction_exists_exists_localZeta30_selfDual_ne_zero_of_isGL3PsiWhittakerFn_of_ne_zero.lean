-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_exists_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cc1b45bf-1355-57f6-8d4e-1ab7b685a95f

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_exists_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open scoped WithZero Pointwise Topology

namespace LTZeta30

section Valuation

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v

theorem exists_uniformizer :
    ∃ ϖ : F, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : F),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

variable {v}

theorem uniformizer_ne_zero {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) :
    Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_add_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem v_mul_le {x y : F} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a) (hy : Valued.v y ≤ WithZero.exp b) :
    Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem v_ne_zero_iff {x : F} : Valued.v x ≠ 0 ↔ x ≠ 0 := by
  rw [ne_eq, Valuation.zero_iff]

theorem exp_log_v {x : F} (hx : x ≠ 0) : WithZero.exp (WithZero.log (Valued.v x)) = Valued.v x :=
  WithZero.exp_log (v_ne_zero_iff.mpr hx)

theorem eq_zero_of_forall_v_le (x : F) (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n : ℤ) + 1))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v x) with hL
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat)
  rw [hxL, WithZero.exp_le_exp] at this
  omega

theorem v_eq_one_of_sub_one_le {x : F} {c : ℤ} (hc : c < 0) (hx : Valued.v (x - 1) ≤ WithZero.exp c) :
    Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  refine Valuation.map_one_add_of_lt _ (hx.trans_lt ?_)
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; exact hc

variable (v) in

def ballSub (m : ℤ) : AddSubgroup F where
  carrier := {x | Valued.v x ≤ WithZero.exp m}
  add_mem' hx hy := v_add_le hx hy
  zero_mem' := by simp
  neg_mem' hx := by simpa only [Set.mem_setOf_eq, Valuation.map_neg] using hx

theorem mem_ballSub {m : ℤ} {x : F} : x ∈ ballSub v m ↔ Valued.v x ≤ WithZero.exp m := Iff.rfl

theorem coe_ballSub (m : ℤ) : (ballSub v m : Set F) = {x | Valued.v x ≤ WithZero.exp m} := rfl

theorem ballSub_mono {m m' : ℤ} (h : m ≤ m') : ballSub v m ≤ ballSub v m' := fun _ hx =>
  le_trans (mem_ballSub.mp hx) (WithZero.exp_le_exp.mpr h)

theorem isOpen_ballSub (m : ℤ) : IsOpen (ballSub v m : Set F) := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer v
  have hset : (ballSub v m : Set F) =
      (fun x => ϖ ^ m * x) ⁻¹' (v.adicCompletionIntegers K : Set F) := by
    ext x
    simp only [coe_ballSub, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow hϖ,
      WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem isClosed_ballSub (m : ℤ) : IsClosed (ballSub v m : Set F) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_ballSub m)

theorem isCompact_ballSub (m : ℤ) : IsCompact (ballSub v m : Set F) := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer v
  have hϖ0 := uniformizer_ne_zero hϖ
  have hO : IsCompact (v.adicCompletionIntegers K : Set F) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)
  have hset : (ballSub v m : Set F) = (fun x => ϖ ^ (-m) * x) '' (v.adicCompletionIntegers K : Set F) := by
    ext x
    simp only [coe_ballSub, Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro h
      refine ⟨ϖ ^ m * x, ?_, ?_⟩
      · rw [Valuation.map_mul, v_uniformizer_zpow hϖ, WithZero.exp_neg]
        calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
              mul_le_mul_right h _
          _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
      · rw [← mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, one_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [Valuation.map_mul, v_uniformizer_zpow hϖ, neg_neg]
      calc WithZero.exp m * Valued.v y ≤ WithZero.exp m * 1 := mul_le_mul_right hy _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact hO.image (continuous_const_mul _)

theorem exists_ballSub_subset_of_mem_nhds {U : Set F} (hU : U ∈ 𝓝 (0 : F)) :
    ∃ m : ℤ, (ballSub v m : Set F) ⊆ U := by
  have hdir : Directed (fun x1 x2 : Set F => x1 ⊇ x2)
      fun n : ℕ => (ballSub v (-((n : ℤ) + 1)) : Set F) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact fun x hx => ballSub_mono (by push_cast; omega) hx
    · exact fun x hx => ballSub_mono (by push_cast; omega) hx
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' hdir (fun n => isCompact_ballSub _)
    (fun n => isClosed_ballSub _) (U := U) (by
      intro x hx
      rw [Set.mem_iInter] at hx
      have : x = 0 := eq_zero_of_forall_v_le x fun n => hx n
      subst this
      exact hU)
  exact ⟨_, hn⟩

theorem exists_ball_subset_of_isOpen {O : Set F} (hO : IsOpen O) {x : F} (hx : x ∈ O) (m₀ : ℤ) :
    ∃ m : ℤ, m ≤ m₀ ∧ ∀ y : F, Valued.v (y - x) ≤ WithZero.exp m → y ∈ O := by
  have h0 : (fun z : F => z + x) ⁻¹' O ∈ 𝓝 (0 : F) := by
    refine (hO.preimage (continuous_add_right x)).mem_nhds ?_
    simpa using hx
  obtain ⟨m, hm⟩ := exists_ballSub_subset_of_mem_nhds h0
  refine ⟨min m m₀, min_le_right _ _, fun y hy => ?_⟩
  have : y - x ∈ ballSub v m := ballSub_mono (min_le_left _ _) hy
  simpa using hm this

variable (v) in

def ball (x : F) (k : ℤ) : Set F := {y | Valued.v (y - x) ≤ WithZero.exp k}

theorem mem_ball {x y : F} {k : ℤ} : y ∈ ball v x k ↔ Valued.v (y - x) ≤ WithZero.exp k := Iff.rfl

theorem self_mem_ball (x : F) (k : ℤ) : x ∈ ball v x k := by simp [ball]

theorem mem_ball_comm {x y : F} {k : ℤ} : y ∈ ball v x k ↔ x ∈ ball v y k := by
  rw [mem_ball, mem_ball, Valuation.map_sub_swap]

theorem ball_subset_ball {x y : F} {k : ℤ} (h : y ∈ ball v x k) : ball v y k ⊆ ball v x k := by
  intro z hz
  rw [mem_ball] at h hz ⊢
  have : z - x = (z - y) + (y - x) := by ring
  rw [this]; exact v_add_le hz h

theorem ball_eq_ball {x y : F} {k : ℤ} (h : y ∈ ball v x k) : ball v y k = ball v x k :=
  Set.Subset.antisymm (ball_subset_ball h) (ball_subset_ball (mem_ball_comm.mp h))

theorem ball_mono {x : F} {k k' : ℤ} (h : k ≤ k') : ball v x k ⊆ ball v x k' := fun _ hy =>
  le_trans (mem_ball.mp hy) (WithZero.exp_le_exp.mpr h)

theorem ball_eq_preimage (x : F) (k : ℤ) : ball v x k = (fun y => y - x) ⁻¹' (ballSub v k : Set F) := rfl

theorem isOpen_ball' (x : F) (k : ℤ) : IsOpen (ball v x k) := by
  rw [ball_eq_preimage]; exact (isOpen_ballSub k).preimage (continuous_sub_right x)

end Valuation

section Quot

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => HeightOneSpectrum.adicCompletion K v

abbrev BQ (m m' : ℤ) : Type := (ballSub v m) ⧸ (ballSub v m').addSubgroupOf (ballSub v m)

scoped instance finite_BQ (m m' : ℤ) : Finite (BQ v m m') := by
  haveI : CompactSpace (ballSub v m) := isCompact_iff_compactSpace.mp (isCompact_ballSub m)
  exact AddSubgroup.quotient_finite_of_isOpen _
    (AddSubgroup.addSubgroupOf_isOpen _ _ (isOpen_ballSub m'))

scoped instance fintype_BQ (m m' : ℤ) : Fintype (BQ v m m') := Fintype.ofFinite _

variable {v}

def rep {m m' : ℤ} (q : BQ v m m') : F := ((Quotient.out q : ballSub v m) : F)

theorem v_rep_le {m m' : ℤ} (q : BQ v m m') : Valued.v (rep q) ≤ WithZero.exp m := (Quotient.out q).2

theorem mk_out {m m' : ℤ} (q : BQ v m m') : (↑(Quotient.out q) : BQ v m m') = q :=
  QuotientAddGroup.out_eq' q

theorem mk_eq_mk_iff {m m' : ℤ} (a b : ballSub v m) :
    ((a : BQ v m m') = b) ↔ Valued.v ((b : F) - a) ≤ WithZero.exp m' := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, mem_ballSub]
  simp [neg_add_eq_sub]

theorem v_sub_rep_mk_le {m m' : ℤ} (c : ballSub v m) :
    Valued.v ((c : F) - rep (c : BQ v m m')) ≤ WithZero.exp m' := by
  have h : ((Quotient.out (c : BQ v m m') : ballSub v m) : BQ v m m') = c := mk_out _
  exact (mk_eq_mk_iff _ _).mp h

theorem eq_of_v_rep_sub_rep_le {m m' : ℤ} {q q' : BQ v m m'}
    (h : Valued.v (rep q - rep q') ≤ WithZero.exp m') : q = q' := by
  rw [← mk_out q, ← mk_out q']
  rw [mk_eq_mk_iff, Valuation.map_sub_swap]
  exact h

theorem v_rep_add_le {m m' : ℤ} (q q' : BQ v m m') :
    Valued.v (rep (q + q') - (rep q + rep q')) ≤ WithZero.exp m' := by
  have h : ((Quotient.out q + Quotient.out q' : ballSub v m) : BQ v m m') =
      ((Quotient.out (q + q') : ballSub v m) : BQ v m m') := by
    rw [QuotientAddGroup.mk_add, mk_out, mk_out, mk_out]
  have := (mk_eq_mk_iff _ _).mp h
  simpa [rep] using this

theorem v_rep_zero_le {m m' : ℤ} : Valued.v (rep (0 : BQ v m m')) ≤ WithZero.exp m' := by
  have h : ((0 : ballSub v m) : BQ v m m') = ((Quotient.out (0 : BQ v m m') : ballSub v m) : BQ v m m') := by
    rw [QuotientAddGroup.mk_zero, mk_out]
  have := (mk_eq_mk_iff _ _).mp h
  simpa [rep] using this

def theta (ψ : AddChar F ℂ) (m m' : ℤ) (z : F) (hz : ∀ d : F, Valued.v d ≤ WithZero.exp m' → ψ (z * d) = 1) :
    AddChar (BQ v m m') ℂ where
  toFun q := ψ (z * rep q)
  map_zero_eq_one' := by
    show ψ (z * rep (0 : BQ v m m')) = 1
    exact hz _ v_rep_zero_le
  map_add_eq_mul' q q' := by
    show ψ (z * rep (q + q')) = ψ (z * rep q) * ψ (z * rep q')
    have h := hz _ (v_rep_add_le q q')
    have : z * rep (q + q') = (z * rep q + z * rep q') + z * (rep (q + q') - (rep q + rep q')) := by ring
    rw [this, AddChar.map_add_eq_mul, h, mul_one, AddChar.map_add_eq_mul]

theorem theta_apply (ψ : AddChar F ℂ) (m m' : ℤ) (z : F) (hz : ∀ d : F, Valued.v d ≤ WithZero.exp m' → ψ (z * d) = 1)
    (q : BQ v m m') : theta ψ m m' z hz q = ψ (z * rep q) := rfl

theorem theta_eq_one_iff (ψ : AddChar F ℂ) (m m' : ℤ) (z : F) (hz : ∀ d : F, Valued.v d ≤ WithZero.exp m' → ψ (z * d) = 1) :
    theta ψ m m' z hz = 1 ↔ ∀ c : F, Valued.v c ≤ WithZero.exp m → ψ (z * c) = 1 := by
  constructor
  · intro h c hc
    let q : BQ v m m' := ((⟨c, hc⟩ : ballSub v m) : BQ v m m')
    have h1 : theta ψ m m' z hz q = 1 := by rw [h]; rfl
    rw [theta_apply] at h1
    have h2 := hz _ (v_sub_rep_mk_le (m' := m') (⟨c, hc⟩ : ballSub v m))
    have : z * c = z * rep q + z * ((c : F) - rep q) := by ring
    rw [this, AddChar.map_add_eq_mul, h1, one_mul]
    exact h2
  · intro h
    ext q
    rw [theta_apply, AddChar.one_apply]
    exact h _ (v_rep_le q)

open scoped Classical in

theorem sum_theta (ψ : AddChar F ℂ) {m m' : ℤ} (z : F) (hz : ∀ d : F, Valued.v d ≤ WithZero.exp m' → ψ (z * d) = 1) :
    ∑ q : BQ v m m', ψ (z * rep q) =
      if (∀ c : F, Valued.v c ≤ WithZero.exp m → ψ (z * c) = 1) then (Fintype.card (BQ v m m') : ℂ) else 0 := by
  have : ∑ q : BQ v m m', ψ (z * rep q) = ∑ q, theta ψ m m' z hz q := rfl
  rw [this]
  split_ifs with h
  · exact AddChar.sum_eq_card_of_eq_one ((theta_eq_one_iff ψ m m' z hz).mpr h)
  · exact AddChar.sum_eq_zero_of_ne_one (mt (theta_eq_one_iff ψ m m' z hz).mp h)

theorem exists_level {ψ : AddChar F ℂ} (hψk : ∃ k : ℤ, ∀ x : F, Valued.v x ≤ WithZero.exp k → ψ x = 1) (hψ : ψ ≠ 1) :
    ∃ ℓ : ℤ, (∀ x : F, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp (ℓ + 1) ∧ ψ x ≠ 1 := by
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  have ht0 : t ≠ 0 := by rintro rfl; exact ht (AddChar.map_zero_eq_one ψ)
  obtain ⟨ℓ, hℓ, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m : ℤ => ∀ x : F, Valued.v x ≤ WithZero.exp m → ψ x = 1)
    ⟨WithZero.log (Valued.v t), fun m hm => by
      by_contra hlt
      push Not at hlt
      apply ht (hm t _)
      rw [← exp_log_v ht0, WithZero.exp_le_exp]; exact hlt.le⟩ hψk
  refine ⟨ℓ, hℓ, ?_⟩
  by_contra hne
  push Not at hne
  have := hmax (ℓ + 1) fun x hx => hne x hx
  omega

theorem forall_psi_mul_eq_one_iff {ψ : AddChar F ℂ} {ℓ : ℤ} (hℓ : ∀ x : F, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1)
    (hℓ' : ∃ x : F, Valued.v x ≤ WithZero.exp (ℓ + 1) ∧ ψ x ≠ 1) (k : ℤ) (z : F) :
    (∀ c : F, Valued.v c ≤ WithZero.exp (ℓ - k) → ψ (z * c) = 1) ↔ Valued.v z ≤ WithZero.exp k := by
  constructor
  · intro h
    by_contra hz
    push Not at hz
    obtain ⟨x, hx, hx1⟩ := hℓ'
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hzk : WithZero.exp (k + 1) ≤ Valued.v z := by
      rw [← exp_log_v hz0, WithZero.exp_lt_exp] at hz
      rw [← exp_log_v hz0, WithZero.exp_le_exp]; omega
    apply hx1
    have hc : Valued.v (z⁻¹ * x) ≤ WithZero.exp (ℓ - k) := by
      rw [Valuation.map_mul, map_inv₀]
      have h1 : (Valued.v z)⁻¹ ≤ (WithZero.exp (k + 1))⁻¹ := inv_anti₀ WithZero.exp_pos hzk
      calc (Valued.v z)⁻¹ * Valued.v x ≤ (WithZero.exp (k + 1))⁻¹ * WithZero.exp (ℓ + 1) :=
            mul_le_mul' h1 hx
        _ = WithZero.exp (ℓ - k) := by
            rw [← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
    have := h _ hc
    rwa [← mul_assoc, mul_inv_cancel₀ hz0, one_mul] at this
  · intro hz c hc
    apply hℓ
    have := v_mul_le hz hc
    rwa [add_sub_cancel] at this

theorem exists_synthesis {ψ : AddChar F ℂ} {ℓ : ℤ} (hℓ : ∀ x : F, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1)
    (hℓ' : ∃ x : F, Valued.v x ≤ WithZero.exp (ℓ + 1) ∧ ψ x ≠ 1) {M k : ℤ} (hkM : k ≤ M) {x₀ : F}
    (hx₀ : Valued.v x₀ ≤ WithZero.exp M) :
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → F) (w : ι → ℂ),
      ∀ a : F, Valued.v a ≤ WithZero.exp M →
        ∑ i, w i * ψ (a * r i) = if Valued.v (a - x₀) ≤ WithZero.exp k then 1 else 0 := by
  let Q := BQ v (ℓ - k) (ℓ - M)
  let N : ℂ := (Fintype.card Q : ℂ)
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨Q, inferInstance, fun q => rep q, fun q => ψ (-(x₀ * rep q)) / N, fun a ha => ?_⟩
  set z := a - x₀ with hz
  have hzM : Valued.v z ≤ WithZero.exp M := v_sub_le ha hx₀
  have hzD : ∀ d : F, Valued.v d ≤ WithZero.exp (ℓ - M) → ψ (z * d) = 1 := fun d hd => by
    apply hℓ; have := v_mul_le hzM hd; rwa [add_sub_cancel] at this
  have hterm : ∀ q : Q, ψ (-(x₀ * rep q)) / N * ψ (a * rep q) = N⁻¹ * ψ (z * rep q) := fun q => by
    rw [div_eq_mul_inv, mul_comm _ N⁻¹, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2; rw [hz]; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_theta ψ z hzD, forall_psi_mul_eq_one_iff hℓ hℓ' k z]
  split_ifs
  · exact inv_mul_cancel₀ hN
  · exact mul_zero _

end Quot

section GL3

open LanglandsTunnell.CubicInduction Matrix

variable {A : Type*} [CommRing A]

theorem iotaGL_diagUnitGL2_mul_upperUnipotent3 (a : Aˣ) (y : A) :
    iotaGL (diagUnitGL2 a) * upperUnipotent3 y 0 0 = upperUnipotent3 ((a : A) * y) 0 0 * iotaGL (diagUnitGL2 a) := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, upperUnipotent3_coe, embedMat2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem iotaGL_diagUnitGL2_one : iotaGL (diagUnitGL2 (1 : Aˣ)) = (1 : GL (Fin 3) A) := by
  show iotaGL (diagHom (1 : Aˣ)) = 1
  rw [map_one, map_one]

theorem iotaGL_diagUnitGL2_mul (a b : Aˣ) :
    iotaGL (diagUnitGL2 (a * b)) = iotaGL (diagUnitGL2 a) * (iotaGL (diagUnitGL2 b) : GL (Fin 3) A) := by
  show iotaGL (diagHom (a * b)) = iotaGL (diagHom a) * iotaGL (diagHom b)
  rw [map_mul, map_mul]

end GL3

section Whittaker

open LanglandsTunnell.CubicInduction Matrix

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "G" => GL (Fin 3) (HeightOneSpectrum.adicCompletion K v)

theorem continuous_upperUnipotent3 : Continuous fun z : F => (upperUnipotent3 z 0 0 : G) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Function.comp, upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    have h : ∀ z : F, ((((upperUnipotent3 z 0 0 : G)⁻¹ : G)) : Matrix (Fin 3) (Fin 3) F) =
        !![1, -z, z * 0 - 0; 0, 1, -0; 0, 0, 1] := fun z => rfl
    simp_rw [h]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_iotaGL_diagUnitGL2 : Continuous fun u : Fˣ => (iotaGL (diagUnitGL2 u) : G) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Function.comp, embedMat2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    have h : ∀ u : Fˣ, ((((iotaGL (diagUnitGL2 u) : G)⁻¹ : G)) : Matrix (Fin 3) (Fin 3) F) =
        embedMat2 !![((u⁻¹ : Fˣ) : F), 0; 0, 1] := fun u => rfl
    simp_rw [h]
    fin_cases i <;> fin_cases j <;> simp [embedMat2]
    all_goals first
      | exact continuous_const
      | simpa using (Units.continuous_coe_inv : Continuous fun u : Fˣ => ((u⁻¹ : Fˣ) : F))

theorem whittaker_upperUnipotent3 {ψ : AddChar F ℂ} {W : G → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (x : F) (g : G) :
    W (upperUnipotent3 x 0 0 * g) = ψ x * W g := by
  simpa using hW x 0 0 g

theorem whittaker_diag_unipotent {ψ : AddChar F ℂ} {W : G → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) (a : Fˣ) (y : F)
    (g : G) : W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 y 0 0 * g)) = ψ ((a : F) * y) * W (iotaGL (diagUnitGL2 a) * g) := by
  rw [← mul_assoc, iotaGL_diagUnitGL2_mul_upperUnipotent3, mul_assoc, whittaker_upperUnipotent3 hW]

theorem exists_ball_conj_upperUnipotent3_mem {U : Subgroup G} (hU : IsOpen (U : Set G)) (g₀ : G) :
    ∃ m : ℤ, ∀ z : F, Valued.v z ≤ WithZero.exp m → g₀⁻¹ * upperUnipotent3 z 0 0 * g₀ ∈ U := by
  have hc : Continuous fun z : F => g₀⁻¹ * (upperUnipotent3 z 0 0 : G) * g₀ :=
    (continuous_const.mul continuous_upperUnipotent3).mul continuous_const
  have h0 : (fun z : F => g₀⁻¹ * (upperUnipotent3 z 0 0 : G) * g₀) ⁻¹' (U : Set G) ∈ 𝓝 (0 : F) := by
    refine (hU.preimage hc).mem_nhds ?_
    simp [upperUnipotent3_zero, U.one_mem]
  obtain ⟨m, hm⟩ := exists_ballSub_subset_of_mem_nhds h0
  exact ⟨m, fun z hz => hm hz⟩

theorem exists_ball_conj_diag_mem {U : Subgroup G} (hU : IsOpen (U : Set G)) (g₀ : G) :
    ∃ c : ℤ, ∀ u : Fˣ, Valued.v ((u : F) - 1) ≤ WithZero.exp c → g₀⁻¹ * iotaGL (diagUnitGL2 u) * g₀ ∈ U := by
  have hc : Continuous fun u : Fˣ => g₀⁻¹ * (iotaGL (diagUnitGL2 u) : G) * g₀ :=
    (continuous_const.mul continuous_iotaGL_diagUnitGL2).mul continuous_const
  set S : Set Fˣ := (fun u : Fˣ => g₀⁻¹ * (iotaGL (diagUnitGL2 u) : G) * g₀) ⁻¹' (U : Set G) with hS
  have h1 : S ∈ 𝓝 (1 : Fˣ) := by
    refine (hU.preimage hc).mem_nhds ?_
    simp [iotaGL_diagUnitGL2_one, U.one_mem]
  rw [Units.isEmbedding_val₀.toIsInducing.nhds_eq_comap (1 : Fˣ), Filter.mem_comap] at h1
  obtain ⟨N, hN, hNS⟩ := h1
  rw [Units.val_one] at hN
  have h0 : (fun z : F => z + 1) ⁻¹' N ∈ 𝓝 (0 : F) := by
    refine (continuous_add_right (1 : F)).continuousAt.preimage_mem_nhds ?_
    simpa using hN
  obtain ⟨c, hc'⟩ := exists_ballSub_subset_of_mem_nhds h0
  refine ⟨c, fun u hu => ?_⟩
  have h2 : (u : F) - 1 ∈ (fun z : F => z + 1) ⁻¹' N := hc' hu
  have h3 : (u : F) ∈ N := by simpa using h2
  exact hNS h3

theorem exists_ball_psi_eq_one {ψ : AddChar F ℂ} {W : G → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) (hinv : ∀ k ∈ U, ∀ g : G, W (g * k) = W g) {g₀ : G} (hg₀ : W g₀ ≠ 0) :
    ∃ m : ℤ, ∀ z : F, Valued.v z ≤ WithZero.exp m → ψ z = 1 := by
  obtain ⟨m, hm⟩ := exists_ball_conj_upperUnipotent3_mem hU g₀
  refine ⟨m, fun z hz => ?_⟩
  have h1 := hinv _ (hm z hz) g₀
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, whittaker_upperUnipotent3 hW] at h1
  have : (ψ z - 1) * W g₀ = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hg₀

theorem continuous_psi_of_ball {ψ : AddChar F ℂ} {m : ℤ} (hm : ∀ z : F, Valued.v z ≤ WithZero.exp m → ψ z = 1) :
    Continuous ψ := by
  refine (IsLocallyConstant.iff_eventually_eq ψ).mpr (fun x => ?_) |>.continuous
  have hO : IsOpen (ball v x m) := isOpen_ball' x m
  filter_upwards [hO.mem_nhds (self_mem_ball x m)] with y hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hm _ hy, mul_one]

theorem exists_support_bound {ψ : AddChar F ℂ} {W : G → ℂ} (hW : IsGL3PsiWhittakerFn ψ W) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) (hinv : ∀ k ∈ U, ∀ g : G, W (g * k) = W g) (g₀ : G) {t₀ : F} (ht₀ : ψ t₀ ≠ 1) :
    ∃ M : ℤ, ∀ a : Fˣ, WithZero.exp M ≤ Valued.v (a : F) → W (iotaGL (diagUnitGL2 a) * g₀) = 0 := by
  obtain ⟨m, hm⟩ := exists_ball_conj_upperUnipotent3_mem hU g₀
  have ht0 : t₀ ≠ 0 := by rintro rfl; exact ht₀ (AddChar.map_zero_eq_one ψ)
  set L₀ := WithZero.log (Valued.v t₀) with hL₀
  refine ⟨L₀ - m, fun a ha => ?_⟩
  set z : F := (a : F)⁻¹ * t₀ with hz
  have hvz : Valued.v z ≤ WithZero.exp m := by
    rw [hz, Valuation.map_mul, map_inv₀, ← exp_log_v ht0, ← hL₀]
    have ha' : (Valued.v (a : F))⁻¹ ≤ (WithZero.exp (L₀ - m))⁻¹ := inv_anti₀ WithZero.exp_pos ha
    calc (Valued.v (a : F))⁻¹ * WithZero.exp L₀ ≤ (WithZero.exp (L₀ - m))⁻¹ * WithZero.exp L₀ :=
          mul_le_mul_left ha' _
      _ = WithZero.exp m := by
          rw [← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
  have h1 := hinv _ (hm z hvz) (iotaGL (diagUnitGL2 a) * g₀)
  rw [← mul_assoc, ← mul_assoc, mul_assoc (iotaGL (diagUnitGL2 a)), mul_inv_cancel, mul_one,
    mul_assoc, whittaker_diag_unipotent hW] at h1
  have haz : (a : F) * z = t₀ := by rw [hz, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
  rw [haz] at h1
  have : (ψ t₀ - 1) * W (iotaGL (diagUnitGL2 a) * g₀) = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) ht₀
  · exact h

theorem exists_locConst {W : G → ℂ} {U : Subgroup G} (hU : IsOpen (U : Set G))
    (hinv : ∀ k ∈ U, ∀ g : G, W (g * k) = W g) (g₀ : G) :
    ∃ c : ℤ, ∀ a u : Fˣ, Valued.v ((u : F) - 1) ≤ WithZero.exp c →
      W (iotaGL (diagUnitGL2 (a * u)) * g₀) = W (iotaGL (diagUnitGL2 a) * g₀) := by
  obtain ⟨c, hc⟩ := exists_ball_conj_diag_mem hU g₀
  refine ⟨c, fun a u hu => ?_⟩
  have h1 := hinv _ (hc u hu) (iotaGL (diagUnitGL2 a) * g₀)
  rw [← mul_assoc, ← mul_assoc, mul_assoc (iotaGL (diagUnitGL2 a)), mul_inv_cancel, mul_one,
    ← iotaGL_diagUnitGL2_mul] at h1
  exact h1

end Whittaker

section MeasureEngine

open LanglandsTunnell.TateLocal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v

theorem measurable_val : Measurable (Units.val : Fˣ → F) := measurable_iff_comap_le.mpr le_rfl

theorem measurableSet_preimage_val {S : Set F} (hS : MeasurableSet S) :
    MeasurableSet ((Units.val : Fˣ → F) ⁻¹' S) :=
  measurable_val hS

theorem measurableSet_ball (x : F) (k : ℤ) : MeasurableSet (ball v x k) := (isOpen_ball' x k).measurableSet

theorem integrable_psi_mul {ψ : AddChar F ℂ} (hψ : Continuous ψ) (μ : Measure Fˣ) {I : Fˣ → ℂ}
    (hI : Integrable I μ) {M : ℤ} (hsupp : ∀ a : Fˣ, ¬ Valued.v (a : F) ≤ WithZero.exp M → I a = 0) (t : F) :
    Integrable (fun a : Fˣ => ψ ((a : F) * t) * I a) μ := by
  obtain ⟨C, hC⟩ := (isCompact_ballSub (v := v) M).exists_bound_of_continuousOn
    (f := fun x : F => ψ (x * t)) ((hψ.comp (continuous_mul_right t)).continuousOn)
  set S : Set Fˣ := (Units.val : Fˣ → F) ⁻¹' (ballSub v M : Set F) with hS
  have hSm : MeasurableSet S := measurableSet_preimage_val (isOpen_ballSub M).measurableSet
  set ψ' : Fˣ → ℂ := S.indicator fun a => ψ ((a : F) * t) with hψ'
  have hmeas : Measurable ψ' := by
    refine Measurable.indicator ?_ hSm
    exact (hψ.comp (continuous_mul_right t)).measurable.comp measurable_val
  have heq : (fun a : Fˣ => ψ ((a : F) * t) * I a) = fun a => ψ' a * I a := by
    funext a
    by_cases ha : a ∈ S
    · rw [hψ', Set.indicator_of_mem ha]
    · rw [hψ', Set.indicator_of_notMem ha, hsupp a ha, mul_zero, zero_mul]
  rw [heq]
  refine hI.bdd_mul hmeas.aestronglyMeasurable (c := max C 0) (Filter.Eventually.of_forall fun a => ?_)
  by_cases ha : a ∈ S
  · rw [hψ', Set.indicator_of_mem ha]; exact (hC _ ha).trans (le_max_left _ _)
  · rw [hψ', Set.indicator_of_notMem ha, norm_zero]; exact le_max_right _ _

theorem setIntegral_eq_zero_of_synth {ψ : AddChar F ℂ} (μ : Measure Fˣ) {I : Fˣ → ℂ} {M : ℤ}
    (hsupp : ∀ a : Fˣ, ¬ Valued.v (a : F) ≤ WithZero.exp M → I a = 0)
    {ι : Type} [Fintype ι] (r : ι → F) (w : ι → ℂ) {P : Set F} (hP : MeasurableSet P)
    (hsynth1 : ∀ a : F, Valued.v a ≤ WithZero.exp M → a ∈ P → ∑ i, w i * ψ (a * r i) = 1)
    (hsynth0 : ∀ a : F, Valued.v a ≤ WithZero.exp M → a ∉ P → ∑ i, w i * ψ (a * r i) = 0)
    (hint : ∀ i, Integrable (fun a : Fˣ => ψ ((a : F) * r i) * I a) μ)
    (hzero : ∀ i, ∫ a : Fˣ, ψ ((a : F) * r i) * I a ∂μ = 0) :
    ∫ a in (Units.val : Fˣ → F) ⁻¹' P, I a ∂μ = 0 := by
  have hPm : MeasurableSet ((Units.val : Fˣ → F) ⁻¹' P) := measurableSet_preimage_val hP
  rw [← integral_indicator hPm]
  have heq : (fun a : Fˣ => ((Units.val : Fˣ → F) ⁻¹' P).indicator I a) =
      fun a : Fˣ => ∑ i, w i * (ψ ((a : F) * r i) * I a) := by
    funext a
    have : ∑ i, w i * (ψ ((a : F) * r i) * I a) = (∑ i, w i * ψ ((a : F) * r i)) * I a := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [this]
    by_cases hM : Valued.v (a : F) ≤ WithZero.exp M
    · by_cases ha : (a : F) ∈ P
      · rw [hsynth1 _ hM ha, one_mul, Set.indicator_of_mem (show a ∈ Units.val ⁻¹' P from ha)]
      · rw [hsynth0 _ hM ha, zero_mul, Set.indicator_of_notMem (show a ∉ Units.val ⁻¹' P from ha)]
    · rw [hsupp a hM, mul_zero, Set.indicator_apply_eq_zero.mpr fun _ => hsupp a hM]
  rw [heq, integral_finset_sum _ fun i _ => (hint i).const_mul (w i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, hzero i, mul_zero]

theorem ae_restrict_eq_zero_of_forall_ball (μ : Measure Fˣ) {f : Fˣ → ℂ} (hf : Integrable f μ) (x₁ : F) (c : ℤ)
    (hballs : ∀ x₀ : F, Valued.v (x₀ - x₁) ≤ WithZero.exp c → ∀ k : ℤ, k ≤ c →
      ∫ a in (Units.val : Fˣ → F) ⁻¹' ball v x₀ k, f a ∂μ = 0) :
    f =ᵐ[μ.restrict ((Units.val : Fˣ → F) ⁻¹' ball v x₁ c)] 0 := by
  classical
  set B₁ : Set Fˣ := (Units.val : Fˣ → F) ⁻¹' ball v x₁ c with hB₁
  have hB₁m : MeasurableSet B₁ := measurableSet_preimage_val (measurableSet_ball x₁ c)

  have hopen : ∀ O : Set F, IsOpen O → ∫ a in (Units.val : Fˣ → F) ⁻¹' O ∩ B₁, f a ∂μ = 0 := by
    intro O hO
    set O' := O ∩ ball v x₁ c with hO'
    have hO'o : IsOpen O' := hO.inter (isOpen_ball' x₁ c)
    have hpre : (Units.val : Fˣ → F) ⁻¹' O ∩ B₁ = Units.val ⁻¹' O' := by rw [hO', Set.preimage_inter]
    rw [hpre]

    let T : ℕ → Set F := fun j => {x | ∀ y : F, Valued.v (y - x) ≤ WithZero.exp (c - j) → y ∈ O'}
    have hTsub : ∀ j, T j ⊆ O' := fun j x hx => hx x (self_mem_ball x _)
    have hTball : ∀ j, ∀ x ∈ T j, ball v x (c - j) ⊆ T j := by
      intro j x hx y hy z hz
      exact hx z (ball_subset_ball hy hz)
    have hTopen : ∀ j, IsOpen (T j) := fun j =>
      isOpen_iff_forall_mem_open.mpr fun x hx =>
        ⟨ball v x (c - j), hTball j x hx, isOpen_ball' _ _, self_mem_ball _ _⟩
    have hTmono : Monotone fun j => (Units.val : Fˣ → F) ⁻¹' T j := by
      intro i j hij a ha y hy
      exact ha y (ball_mono (by omega) hy)
    have hTunion : (⋃ j : ℕ, (Units.val : Fˣ → F) ⁻¹' T j) = Units.val ⁻¹' O' := by
      rw [← Set.preimage_iUnion]; congr 1
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset hTsub
      · intro x hx
        obtain ⟨m, hmc, hm⟩ := exists_ball_subset_of_isOpen hO'o hx c
        refine Set.mem_iUnion.mpr ⟨(c - m).toNat, fun y hy => hm y (le_trans hy ?_)⟩
        rw [WithZero.exp_le_exp]; have := Int.self_le_toNat (c - m); omega

    have hTint : ∀ j : ℕ, ∫ a in (Units.val : Fˣ → F) ⁻¹' T j, f a ∂μ = 0 := by
      intro j
      set r : ℤ := c - j with hr
      let ctr : BQ v c r → F := fun q => x₁ + rep q
      have hctr : ∀ q, Valued.v (ctr q - x₁) ≤ WithZero.exp c := fun q => by
        have : ctr q - x₁ = rep q := by simp only [ctr]; ring
        rw [this]; exact v_rep_le q
      let S : Finset (BQ v c r) := Finset.univ.filter fun q => ctr q ∈ T j
      have hdecomp : T j = ⋃ q ∈ S, ball v (ctr q) r := by
        apply Set.Subset.antisymm
        · intro x hx
          have hxB : x ∈ ball v x₁ c := (hTsub j hx).2
          let cx : ballSub v c := ⟨x - x₁, hxB⟩
          let q : BQ v c r := (cx : BQ v c r)
          have hq : Valued.v ((x - x₁) - rep q) ≤ WithZero.exp r := v_sub_rep_mk_le cx
          have hxq : x ∈ ball v (ctr q) r := by
            have : x - ctr q = (x - x₁) - rep q := by simp only [ctr]; ring
            rw [mem_ball, this]; exact hq
          have hcq : ctr q ∈ T j := by
            intro y hy
            have : y ∈ ball v x r := by rw [ball_eq_ball hxq]; exact hy
            exact hx y this
          exact Set.mem_iUnion₂.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcq⟩, hxq⟩
        · intro y hy
          obtain ⟨q, hqS, hyq⟩ := Set.mem_iUnion₂.mp hy
          have hcq : ctr q ∈ T j := (Finset.mem_filter.mp hqS).2
          intro z hz
          exact hcq z (ball_subset_ball hyq hz)
      have hdisj : Set.Pairwise (↑S) (Function.onFun Disjoint fun q => (Units.val : Fˣ → F) ⁻¹' ball v (ctr q) r) := by
        intro q _ q' _ hne
        refine Set.disjoint_left.mpr fun a ha ha' => hne ?_
        apply eq_of_v_rep_sub_rep_le
        have h1 : Valued.v ((a : F) - ctr q) ≤ WithZero.exp r := ha
        have h2 : Valued.v ((a : F) - ctr q') ≤ WithZero.exp r := ha'
        have : rep q - rep q' = ((a : F) - ctr q') - ((a : F) - ctr q) := by simp only [ctr]; ring
        rw [this]; exact v_sub_le h2 h1
      rw [hdecomp, Set.preimage_iUnion₂,
        integral_biUnion_finset S (fun q _ => measurableSet_preimage_val (measurableSet_ball _ _)) hdisj
          (fun q _ => hf.integrableOn)]
      exact Finset.sum_eq_zero fun q _ => hballs (ctr q) (hctr q) r (by omega)
    have hlim := tendsto_setIntegral_of_monotone (μ := μ) (f := f)
      (s := fun j : ℕ => (Units.val : Fˣ → F) ⁻¹' T j)
      (fun j => measurableSet_preimage_val (hTopen j).measurableSet) hTmono hf.integrableOn
    rw [hTunion] at hlim
    have hconst : (fun j : ℕ => ∫ a in (Units.val : Fˣ → F) ⁻¹' T j, f a ∂μ) = fun _ => 0 := funext hTint
    rw [hconst] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

  have hall : ∀ S : Set Fˣ, MeasurableSet S → ∫ a in S ∩ B₁, f a ∂μ = 0 := by
    have h_eq : (inferInstance : MeasurableSpace Fˣ) =
        MeasurableSpace.generateFrom (Set.preimage (Units.val : Fˣ → F) '' {O : Set F | IsOpen O}) := by
      rw [← MeasurableSpace.comap_generateFrom]; rfl
    refine fun S hS => MeasurableSpace.induction_on_inter (C := fun S _ => ∫ a in S ∩ B₁, f a ∂μ = 0)
      h_eq ?_ ?_ ?_ ?_ ?_ S hS
    · rintro _ ⟨O, hO : IsOpen O, rfl⟩ _ ⟨O', hO' : IsOpen O', rfl⟩ _
      exact ⟨O ∩ O', hO.inter hO', rfl⟩
    · simp
    · rintro _ ⟨O, hO : IsOpen O, rfl⟩
      exact hopen O hO
    · intro S hSm hS0
      have huniv : ∫ a in B₁, f a ∂μ = 0 := by
        have := hopen Set.univ isOpen_univ
        rwa [Set.preimage_univ, Set.univ_inter] at this
      have hsplit := integral_inter_add_diff (μ := μ) (f := f) (s := B₁) hSm hf.integrableOn
      rw [Set.inter_comm] at hS0
      rw [hS0, huniv, zero_add] at hsplit
      rwa [Set.diff_eq, Set.inter_comm] at hsplit
    · intro g hdisj hgm hg
      rw [Set.iUnion_inter, integral_iUnion (fun i => (hgm i).inter hB₁m)
        (hdisj.mono fun i j h => h.mono Set.inter_subset_left Set.inter_subset_left) hf.integrableOn]
      simp [hg]

  refine (hf.restrict (s := B₁)).ae_eq_zero_of_forall_setIntegral_eq_zero fun S hS _ => ?_
  rw [Measure.restrict_restrict hS]
  exact hall S hS

theorem modulus_eq_one_of_v_eq_one {x : F} (hx : Valued.v x = 1) : modulus x = 1 := by
  have hx0 : x ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx
  rw [modulus_of_ne_zero hx0]
  set μ := Measure.addHaarMeasure (integersPositiveCompacts K v) with hμ
  have h0 : μ (v.adicCompletionIntegers K : Set F) ≠ 0 :=
    (IsOpen.measure_pos μ (Valued.isOpen_valuationSubring _) ⟨0, (v.adicCompletionIntegers K).zero_mem⟩).ne'
  have htop : μ (v.adicCompletionIntegers K : Set F) ≠ ⊤ := by
    rw [← coe_integersPositiveCompacts]; exact (integersPositiveCompacts K v).isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 htop ?_
  rw [ENNReal.coe_one, one_mul]
  congr 1
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul,
    Valuation.map_mul]
  have : Valued.v (((Units.mk0 x hx0)⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hx, inv_one]
  rw [this, one_mul]

theorem measurableSet_image_val {S : Set Fˣ} (hS : MeasurableSet S) :
    MeasurableSet ((Units.val : Fˣ → F) '' S) := by
  obtain ⟨S', hS', rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
  rw [Set.image_preimage_eq_inter_range]
  refine hS'.inter ?_
  have : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hx; exact ⟨Units.mk0 x hx, rfl⟩
  rw [this]; exact (measurableSet_singleton 0).compl

theorem comap_val_apply (ν : Measure F) {S : Set F} (hS : MeasurableSet S) (h0 : (0 : F) ∉ S) :
    Measure.comap (Units.val : Fˣ → F) ν ((Units.val : Fˣ → F) ⁻¹' S) = ν S := by
  rw [Measure.comap_apply _ Units.val_injective (fun s hs => measurableSet_image_val hs) _
    (measurableSet_preimage_val hS)]
  congr 1
  rw [Set.image_preimage_eq_inter_range]
  apply Set.inter_eq_self_of_subset_left
  intro x hx
  exact ⟨Units.mk0 x (by rintro rfl; exact h0 hx), rfl⟩

theorem mulMeasure_apply_of_v_eq_one (ν : Measure F) {S : Set F} (hS : MeasurableSet S)
    (h1 : ∀ x ∈ S, Valued.v x = 1) : mulMeasure ν S = ν S := by
  have h0 : ∀ x ∈ S, x ≠ 0 := fun x hx h => by
    have := h1 x hx; rw [h, Valuation.map_zero] at this; exact zero_ne_one this
  rw [mulMeasure, withDensity_apply _ hS]
  rw [setLIntegral_congr_fun hS (g := fun _ => 1) (fun x hx => by
    show ((modulus x : ENNReal))⁻¹ = 1
    rw [modulus_eq_one_of_v_eq_one (h1 x hx)]; simp)]
  rw [setLIntegral_one, Measure.restrict_apply hS]
  congr 1
  exact Set.inter_eq_self_of_subset_left fun x hx => h0 x hx

theorem selfDualHaarAt_ne_zero {U : Set F} (hU : IsOpen U) (hne : U.Nonempty) : selfDualHaarAt K v U ≠ 0 := by
  have hq : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  unfold selfDualHaarAt
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  refine mul_ne_zero ?_ ((hU.measure_pos _ hne).ne')
  exact_mod_cast (NNReal.rpow_pos hq).ne'

theorem comap_mulMeasure_selfDual_ball_ne_zero (c : ℤ) (hc : c < 0) :
    Measure.comap (Units.val : Fˣ → F) (mulMeasure (selfDualHaarAt K v))
      ((Units.val : Fˣ → F) ⁻¹' ball v (1 : F) c) ≠ 0 := by
  have hB : MeasurableSet (ball v (1 : F) c) := measurableSet_ball 1 c
  have h1 : ∀ x ∈ ball v (1 : F) c, Valued.v x = 1 := fun x hx => v_eq_one_of_sub_one_le hc hx
  have h0 : (0 : F) ∉ ball v (1 : F) c := fun h => by
    have := h1 0 h; rw [Valuation.map_zero] at this; exact zero_ne_one this
  rw [comap_val_apply _ hB h0, mulMeasure_apply_of_v_eq_one _ hB h1]
  exact selfDualHaarAt_ne_zero (isOpen_ball' 1 c) ⟨1, self_mem_ball 1 c⟩

end MeasureEngine

section Assembly

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ v

theorem convergent_translate {ψ : AddChar F ℂ} (hψc : Continuous ψ) {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {χ : Fˣ →* ℂˣ} {μ : Measure Fˣ} {g₀ : LocalGL3 v} {σ₀ : ℝ}
    (hσ₀ : IsLocalZeta30ConvergentAbove v μ W χ g₀ σ₀) {M : ℤ}
    (hM : ∀ a : Fˣ, WithZero.exp M ≤ Valued.v (a : F) → W (iotaGL (diagUnitGL2 a) * g₀) = 0) (t : F) :
    IsLocalZeta30ConvergentAbove v μ W χ (upperUnipotent3 t 0 0 * g₀) σ₀ := by
  intro s hs
  have hI := hσ₀ s hs
  have hsupp : ∀ a : Fˣ, ¬ Valued.v (a : F) ≤ WithZero.exp M →
      W (iotaGL (diagUnitGL2 a) * g₀) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (s - 1) = 0 :=
    fun a ha => by rw [hM a (le_of_lt (not_le.mp ha)), zero_mul, zero_mul]
  have := integrable_psi_mul hψc μ hI hsupp t
  refine this.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only []
  rw [whittaker_diag_unipotent hW]; ring

theorem engine (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψ W) (hW0 : W ≠ 0)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (χ : Fˣ →* ℂˣ) (μ : Measure Fˣ)
    (hμ : ∀ c : ℤ, c < 0 → μ ((Units.val : Fˣ → F) ⁻¹' ball v (1 : F) c) ≠ 0)
    (hconv : ∀ g : LocalGL3 v, ∃ σ : ℝ, IsLocalZeta30ConvergentAbove v μ W χ g σ) :
    ∃ (g : LocalGL3 v) (σ : ℝ), IsLocalZeta30ConvergentAbove v μ W χ g σ ∧
      ∃ s : ℂ, σ < s.re ∧ localZeta30 v μ W χ s g ≠ 0 := by
  classical
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, W g₀ ≠ 0 := Function.ne_iff.mp hW0
  obtain ⟨U, hU, hinv⟩ := hsm
  obtain ⟨σ₀, hσ₀⟩ := hconv g₀
  obtain ⟨m₀, hm₀⟩ := exists_ball_psi_eq_one hW hU hinv hg₀
  obtain ⟨t₀, ht₀⟩ := AddChar.ne_one_iff.mp hψ
  have hψc : Continuous ψ := continuous_psi_of_ball hm₀
  obtain ⟨ℓ, hℓ, hℓ'⟩ := exists_level ⟨m₀, hm₀⟩ hψ
  obtain ⟨M, hM⟩ := exists_support_bound hW hU hinv g₀ ht₀
  obtain ⟨c, hc⟩ := exists_locConst (W := W) hU hinv g₀
  have hM0 : 0 < M := by
    by_contra h
    push Not at h
    apply hg₀
    have := hM 1 (by
      rw [Units.val_one, Valuation.map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]; exact h)
    rwa [iotaGL_diagUnitGL2_one, one_mul] at this
  have hconvt : ∀ t : F, IsLocalZeta30ConvergentAbove v μ W χ (upperUnipotent3 t 0 0 * g₀) σ₀ :=
    fun t => convergent_translate hψc hW hσ₀ hM t
  by_contra Hne
  have hzero : ∀ (t : F) (s : ℂ), σ₀ < s.re → localZeta30 v μ W χ s (upperUnipotent3 t 0 0 * g₀) = 0 := by
    intro t s hs
    by_contra h
    exact Hne ⟨_, σ₀, hconvt t, s, hs, h⟩
  set s₀ : ℂ := ((σ₀ + 1 : ℝ) : ℂ) with hs₀def
  have hs₀ : σ₀ < s₀.re := by simp [hs₀def]
  set I : Fˣ → ℂ := fun a => W (iotaGL (diagUnitGL2 a) * g₀) * ((χ a : ℂˣ) : ℂ) *
    ((modulus (a : F) : ℝ) : ℂ) ^ (s₀ - 1) with hIdef
  have hI : Integrable I μ := hσ₀ s₀ hs₀
  have hIsupp : ∀ a : Fˣ, ¬ Valued.v (a : F) ≤ WithZero.exp M → I a = 0 := fun a ha => by
    simp only [hIdef]; rw [hM a (le_of_lt (not_le.mp ha)), zero_mul, zero_mul]
  set c' : ℤ := min c (-1) with hc'def
  have hc'0 : c' < 0 := by omega

  have hballs : ∀ x₀ : F, Valued.v (x₀ - 1) ≤ WithZero.exp c' → ∀ k : ℤ, k ≤ c' →
      ∫ a in (Units.val : Fˣ → F) ⁻¹' ball v x₀ k, I a ∂μ = 0 := by
    intro x₀ hx₀ k hk
    have hvx₀ : Valued.v x₀ ≤ WithZero.exp M := by
      rw [v_eq_one_of_sub_one_le hc'0 hx₀, ← WithZero.exp_zero, WithZero.exp_le_exp]; exact hM0.le
    have hkM : k ≤ M := by omega
    obtain ⟨ι, _, r, w, hsynth⟩ := exists_synthesis hℓ hℓ' hkM hvx₀
    refine setIntegral_eq_zero_of_synth (ψ := ψ) μ hIsupp r w (measurableSet_ball x₀ k) ?_ ?_ ?_ ?_
    · intro a ha haP
      have := hsynth a ha
      rwa [if_pos (show Valued.v (a - x₀) ≤ WithZero.exp k from haP)] at this
    · intro a ha haP
      have := hsynth a ha
      rwa [if_neg (show ¬ Valued.v (a - x₀) ≤ WithZero.exp k from haP)] at this
    · exact fun i => integrable_psi_mul hψc μ hI hIsupp (r i)
    · intro i
      rw [← hzero (r i) s₀ hs₀]
      simp only [localZeta30, hIdef]
      congr 1
      funext a
      rw [whittaker_diag_unipotent hW]; ring
  have hae := ae_restrict_eq_zero_of_forall_ball μ hI 1 c' hballs
  have hB₁m : MeasurableSet ((Units.val : Fˣ → F) ⁻¹' ball v (1 : F) c') :=
    measurableSet_preimage_val (measurableSet_ball 1 c')

  have hne : ∀ a : Fˣ, a ∈ (Units.val : Fˣ → F) ⁻¹' ball v (1 : F) c' → I a ≠ 0 := by
    intro a ha
    have hφ : W (iotaGL (diagUnitGL2 a) * g₀) = W g₀ := by
      have := hc 1 a (le_trans ha (WithZero.exp_le_exp.mpr (min_le_left _ _)))
      rwa [one_mul, iotaGL_diagUnitGL2_one, one_mul] at this
    simp only [hIdef]
    refine mul_ne_zero (mul_ne_zero ?_ (Units.ne_zero _)) ?_
    · rwa [hφ]
    · rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      exact Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (modulus_ne_zero a.ne_zero))
  apply hμ c' hc'0
  rw [measure_eq_zero_iff_ae_notMem]
  have h2 := (ae_restrict_iff' hB₁m).mp hae
  filter_upwards [h2] with a ha hmem
  exact hne a hmem (ha hmem)

end Assembly

end LTZeta30
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_exists_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero.LTZeta30"

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
theorem solution
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW0 : W ≠ 0)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hconv : ∀ g : LocalGL3 v, ∃ σ : ℝ,
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ) :
    letI := localBorel ℚ v
    (∃ (g : LocalGL3 v) (σ : ℝ),
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ ∧
      ∃ s : ℂ, σ < s.re ∧
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g ≠ 0) :=
  LTZeta30.engine ψv hψv W hW hW0 hsm χ _
    (fun c hc => LTZeta30.comap_mulMeasure_selfDual_ball_ne_zero c hc) hconv

end
end S_LanglandsTunnell_CubicInduction_exists_exists_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_exists_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero (solution)
