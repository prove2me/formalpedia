-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_subgroups_shells_finset_card_le_of_units_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8d3e0fd9-158e-589a-977a-9d17c5fabf43

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace ShellGeo

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)

def q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_q : 1 < q K v := by
  unfold q; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem q_pos : 0 < q K v := one_pos.trans (one_lt_q K v)

theorem exists_norm_eq_zpow (x : F) (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = q K v ^ n := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  rfl

theorem exists_norm_eq_q : ∃ u : F, ‖u‖ = q K v := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hn : ‖((π : K) : F)‖ = (q K v)⁻¹ := by
    have h := NumberField.FinitePlace.norm_embedding' (v := v) (π : K)
    rw [NumberField.FinitePlace.embedding_apply] at h
    rw [h, hπ, show (WithZero.exp (-1 : ℤ)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe]
    unfold q
    push_cast
    simp [zpow_neg, zpow_one]
  refine ⟨((π : K) : F)⁻¹, ?_⟩
  rw [norm_inv, hn, inv_inv]

theorem norm_eq_one_of_norm_sub_one_lt {t : F} (h : ‖t - 1‖ < 1) : ‖t‖ = 1 := by
  have hne : ‖(1 : F)‖ ≠ ‖t - 1‖ := by rw [norm_one]; exact (ne_of_lt h).symm
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [add_sub_cancel, norm_one] at this
  rw [this]
  exact max_eq_left h.le

def ballSub (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) : Subgroup Fˣ where
  carrier := {t | ‖(t : F) - 1‖ ≤ r}
  one_mem' := by
    show ‖((1 : Fˣ) : F) - 1‖ ≤ r
    rw [Units.val_one, sub_self, norm_zero]
    exact hr0
  mul_mem' := by
    intro s t hs ht
    change ‖(s : F) - 1‖ ≤ r at hs
    change ‖(t : F) - 1‖ ≤ r at ht
    show ‖((s * t : Fˣ) : F) - 1‖ ≤ r
    have hs1 : ‖(s : F)‖ = 1 := norm_eq_one_of_norm_sub_one_lt K v (hs.trans_lt hr)
    have : ((s * t : Fˣ) : F) - 1 = (s : F) * ((t : F) - 1) + ((s : F) - 1) := by push_cast; ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hs)
    rw [norm_mul, hs1, one_mul]; exact ht
  inv_mem' := by
    intro t ht
    change ‖(t : F) - 1‖ ≤ r at ht
    show ‖((t⁻¹ : Fˣ) : F) - 1‖ ≤ r
    have ht1 : ‖(t : F)‖ = 1 := norm_eq_one_of_norm_sub_one_lt K v (ht.trans_lt hr)
    have : ((t⁻¹ : Fˣ) : F) - 1 = -(((t⁻¹ : Fˣ) : F) * ((t : F) - 1)) := by
      rw [mul_sub, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]; ring
    rw [this, norm_neg, norm_mul, Units.val_inv_eq_inv_val, norm_inv, ht1, inv_one, one_mul]
    exact ht

theorem mem_ballSub_iff {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : Fˣ) : t ∈ ballSub K v r hr0 hr ↔ ‖(t : F) - 1‖ ≤ r := Iff.rfl

theorem norm_eq_one_of_mem_ballSub {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {t : Fˣ} (ht : t ∈ ballSub K v r hr0 hr) : ‖(t : F)‖ = 1 :=
  norm_eq_one_of_norm_sub_one_lt K v (lt_of_le_of_lt ht hr)

theorem isOpen_ballSub {r : ℝ} (hr0 : 0 ≤ r) (hr0' : 0 < r) (hr : r < 1) : IsOpen (ballSub K v r hr0 hr : Set Fˣ) := by
  have : (ballSub K v r hr0 hr : Set Fˣ) = (Units.val : Fˣ → F) ⁻¹' Metric.closedBall (1 : F) r := by
    ext t; simp [mem_ballSub_iff, Metric.mem_closedBall, dist_eq_norm]
  rw [this]
  exact (IsUltrametricDist.isOpen_closedBall (1 : F) hr0'.ne').preimage Units.continuous_val

theorem isCompact_preimage_val {C : Set F} (hC : IsCompact C) (h0 : (0 : F) ∉ C) :
    IsCompact ((Units.val : Fˣ → F) ⁻¹' C) := by
  rw [Units.isOpenEmbedding_val.isEmbedding.isCompact_iff, Set.image_preimage_eq_of_subset]
  · exact hC
  · intro x hx
    exact ⟨Units.mk0 x (fun h => h0 (h ▸ hx)), rfl⟩

theorem isCompact_ballSub {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : IsCompact (ballSub K v r hr0 hr : Set Fˣ) := by
  have : (ballSub K v r hr0 hr : Set Fˣ) = (Units.val : Fˣ → F) ⁻¹' Metric.closedBall (1 : F) r := by
    ext t; simp [mem_ballSub_iff, Metric.mem_closedBall, dist_eq_norm]
  rw [this]
  refine isCompact_preimage_val K v (isCompact_closedBall _ _) (fun h => ?_)
  rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, norm_one] at h
  exact absurd (h.trans_lt hr) (lt_irrefl _)

theorem exists_finset_reps (H : Subgroup Fˣ) (hH : IsOpen (H : Set Fˣ)) (S : Set Fˣ) (hS : IsCompact S) :
    ∃ R : Finset Fˣ, (↑R ⊆ S) ∧ (∀ τ ∈ R, ∀ τ' ∈ R, τ ≠ τ' → τ⁻¹ * τ' ∉ H) ∧
      ∀ t ∈ S, ∃ τ ∈ R, t⁻¹ * τ ∈ H := by
  classical

  have hcov : S ⊆ ⋃ s ∈ S, (fun t : Fˣ => s⁻¹ * t) ⁻¹' (H : Set Fˣ) := by
    intro s hs
    exact Set.mem_biUnion hs (by simp [H.one_mem])
  have hop : ∀ s ∈ S, IsOpen ((fun t : Fˣ => s⁻¹ * t) ⁻¹' (H : Set Fˣ)) :=
    fun s _ => hH.preimage (continuous_const_mul s⁻¹)
  obtain ⟨T, hTS, hTfin, hTcov⟩ := hS.elim_finite_subcover_image hop hcov

  let Q : Finset (Fˣ ⧸ H) := hTfin.toFinset.image (QuotientGroup.mk (s := H))
  have hrep : ∀ c ∈ Q, ∃ s ∈ T, (QuotientGroup.mk s : Fˣ ⧸ H) = c := by
    intro c hc
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨s, hTfin.mem_toFinset.mp hs, rfl⟩
  choose rep hrepT hrepmk using hrep
  let R : Finset Fˣ := Q.attach.image fun c => rep c.1 c.2
  refine ⟨R, ?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hτ
    exact hTS (hrepT c.1 c.2)
  · intro τ hτ τ' hτ' hne hmem
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hτ'
    apply hne
    have hcc : c.1 = c'.1 := by
      rw [← hrepmk c.1 c.2, ← hrepmk c'.1 c'.2]
      exact QuotientGroup.eq.mpr hmem
    have : c = c' := Subtype.ext hcc
    rw [this]
  · intro t ht
    have := hTcov ht
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop] at this
    obtain ⟨s, hsT, hst⟩ := this
    have hc : (QuotientGroup.mk s : Fˣ ⧸ H) ∈ Q :=
      Finset.mem_image.mpr ⟨s, hTfin.mem_toFinset.mpr hsT, rfl⟩
    refine ⟨rep _ hc, Finset.mem_image.mpr ⟨⟨_, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rw [← QuotientGroup.eq, hrepmk _ hc]
    exact (QuotientGroup.eq.mpr hst).symm

theorem inv_mul_mem_ballSub_iff {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {a b : Fˣ} (ha : ‖(a : F)‖ = 1) :
    a⁻¹ * b ∈ ballSub K v r hr0 hr ↔ ‖(b : F) - (a : F)‖ ≤ r := by
  rw [mem_ballSub_iff]
  have : ((a⁻¹ * b : Fˣ) : F) - 1 = ((a⁻¹ : Fˣ) : F) * ((b : F) - (a : F)) := by
    rw [mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this, norm_mul, Units.val_inv_eq_inv_val, norm_inv, ha, inv_one, one_mul]

theorem zpow_lt_one_of_neg {n : ℤ} (hn : n < 0) : q K v ^ n < 1 :=
  zpow_lt_one_of_neg₀ (one_lt_q K v) hn

end ShellGeo

end

open ShellGeo in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n₀ c : ℕ) (hn₀ : 1 ≤ n₀) (hc : 1 ≤ c) :
    ∃ (U₁ A : Subgroup (v.adicCompletion K)ˣ) (V : ℕ → Subgroup (v.adicCompletion K)ˣ) (sh : ℕ → Set (v.adicCompletion K)ˣ) (M₀ : ℕ),
      IsOpen (U₁ : Set (v.adicCompletion K)ˣ) ∧ IsCompact (U₁ : Set (v.adicCompletion K)ˣ) ∧
      IsOpen (A : Set (v.adicCompletion K)ˣ) ∧ IsCompact (A : Set (v.adicCompletion K)ˣ) ∧
      (∀ k, IsOpen (V k : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, V k ≤ U₁) ∧ (∀ k, V k ≤ A) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ ↔ ‖(t : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n₀ : ℤ))) ∧
      (∀ a : (v.adicCompletion K)ˣ, a ∈ A ↔ ‖(a : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(c : ℤ))) ∧
      (∀ (k : ℕ) (τ : (v.adicCompletion K)ˣ), τ ∈ V k ↔
        ‖(τ : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k + n₀ + c : ℕ) : ℤ))) ∧
      (∀ (k : ℕ) (t : (v.adicCompletion K)ˣ), t ∈ sh k ↔
        ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k + n₀ : ℕ) : ℤ))) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → ‖(t : (v.adicCompletion K))‖ = 1) ∧
      (∀ k, IsCompact (sh k)) ∧ (∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh k) ∧
      (Pairwise fun k k' => Disjoint (sh k) (sh k')) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ≠ 1 → ∃ k, t ∈ sh k) ∧
      (∀ k, ∀ t ∈ sh k, ∀ τ ∈ V k, t * τ ∈ sh k) ∧
      (∀ k, ∃ Ft : Finset (v.adicCompletion K)ˣ, Ft.card ≤ M₀ ∧ (↑Ft ⊆ sh k) ∧
        (∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V k) ∧
        ∀ t ∈ sh k, ∃ τ ∈ Ft, t⁻¹ * τ ∈ V k) ∧
      (∀ S : Set (v.adicCompletion K)ˣ, IsCompact S → ∃ Fa : Finset (v.adicCompletion K)ˣ,
        (∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A) ∧ ∀ a ∈ S, ∃ α ∈ Fa, a⁻¹ * α ∈ A) := by
  classical
  set qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqv
  have hq1 : 1 < qv := one_lt_q K v
  have hq0 : 0 < qv := q_pos K v

  have hrad : ∀ m : ℕ, 1 ≤ m → 0 ≤ qv ^ (-(m : ℤ)) ∧ 0 < qv ^ (-(m : ℤ)) ∧ qv ^ (-(m : ℤ)) < 1 := fun m hm =>
    ⟨(zpow_pos hq0 _).le, zpow_pos hq0 _, zpow_lt_one_of_neg₀ hq1 (by omega)⟩
  obtain ⟨hU0, hU0', hU1⟩ := hrad n₀ hn₀
  obtain ⟨hA0, hA0', hA1⟩ := hrad c hc
  have hV := fun k : ℕ => hrad (k + n₀ + c) (by omega)
  let U₁ : Subgroup (v.adicCompletion K)ˣ := ballSub K v (qv ^ (-(n₀ : ℤ))) hU0 hU1
  let A : Subgroup (v.adicCompletion K)ˣ := ballSub K v (qv ^ (-(c : ℤ))) hA0 hA1
  let V : ℕ → Subgroup (v.adicCompletion K)ˣ := fun k =>
    ballSub K v (qv ^ (-((k + n₀ + c : ℕ) : ℤ))) (hV k).1 (hV k).2.2
  let sh : ℕ → Set (v.adicCompletion K)ˣ := fun k =>
    {t | ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ = qv ^ (-((k + n₀ : ℕ) : ℤ))}

  have hsh_norm : ∀ k, ∀ t ∈ sh k, ‖(t : v.adicCompletion K) - 1‖ = qv ^ (-((k + n₀ : ℕ) : ℤ)) := by
    intro k t ht; rw [norm_sub_rev]; exact ht
  have hsh_U : ∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ) := by
    intro k t ht
    show ‖(t : v.adicCompletion K) - 1‖ ≤ qv ^ (-(n₀ : ℤ))
    rw [hsh_norm k t ht]
    exact zpow_le_zpow_right₀ hq1.le (by push_cast; omega)
  have hU_one : ∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → ‖(t : v.adicCompletion K)‖ = 1 :=
    fun t ht => norm_eq_one_of_mem_ballSub K v hU0 hU1 ht
  have hsh_one : ∀ k, ∀ t ∈ sh k, ‖(t : v.adicCompletion K)‖ = 1 := fun k t ht => hU_one t (hsh_U k ht)
  have hsh_cpt : ∀ k, IsCompact (sh k) := by
    intro k
    have : sh k = (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) ⁻¹'
        Metric.sphere (1 : v.adicCompletion K) (qv ^ (-((k + n₀ : ℕ) : ℤ))) := by
      ext t; simp [sh, norm_sub_rev]
    rw [this]
    refine isCompact_preimage_val K v (isCompact_sphere _ _) (fun h => ?_)
    rw [Metric.mem_sphere, dist_eq_norm, zero_sub, norm_neg, norm_one] at h
    exact absurd (hrad (k + n₀) (by omega)).2.2 (by rw [← h]; exact lt_irrefl _)

  obtain ⟨u, hu⟩ := exists_norm_eq_q K v
  have hu' : ‖u‖ = qv := hu

  have hreps := fun k : ℕ => exists_finset_reps K v (V k) (isOpen_ballSub K v (hV k).1 (hV k).2.1 (hV k).2.2) (sh k) (hsh_cpt k)
  choose Ft hFt_sub hFt_ne hFt_cov using hreps
  refine ⟨U₁, A, V, sh, (Ft 0).card, isOpen_ballSub K v hU0 hU0' hU1, isCompact_ballSub K v hU0 hU1,
    isOpen_ballSub K v hA0 hA0' hA1, isCompact_ballSub K v hA0 hA1,
    fun k => isOpen_ballSub K v (hV k).1 (hV k).2.1 (hV k).2.2, ?_, ?_,
    fun t => Iff.rfl, fun a => Iff.rfl, fun k τ => Iff.rfl, fun k t => Iff.rfl, hU_one,
    hsh_cpt, hsh_U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro k t ht
    show ‖(t : v.adicCompletion K) - 1‖ ≤ qv ^ (-(n₀ : ℤ))
    exact le_trans ht (zpow_le_zpow_right₀ hq1.le (by push_cast; omega))
  ·
    intro k t ht
    show ‖(t : v.adicCompletion K) - 1‖ ≤ qv ^ (-(c : ℤ))
    exact le_trans ht (zpow_le_zpow_right₀ hq1.le (by push_cast; omega))
  ·
    intro k h
    have h' : ‖(1 : v.adicCompletion K) - ((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
        qv ^ (-((k + n₀ : ℕ) : ℤ)) := h
    rw [Units.val_one, sub_self, norm_zero] at h'
    exact absurd h' (ne_of_lt (zpow_pos hq0 _))
  ·
    intro k k' hkk
    refine Set.disjoint_left.mpr fun t h1 h2 => hkk ?_
    have h1' : ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ = qv ^ (-((k + n₀ : ℕ) : ℤ)) := h1
    have h2' : ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ = qv ^ (-((k' + n₀ : ℕ) : ℤ)) := h2
    have := zpow_right_injective₀ hq0 hq1.ne' (h1'.symm.trans h2')
    push_cast at this
    omega
  ·
    intro t ht hne
    have hx : (1 : v.adicCompletion K) - (t : v.adicCompletion K) ≠ 0 := by
      intro h
      apply hne
      apply Units.ext
      rw [Units.val_one]
      exact (sub_eq_zero.mp h).symm
    obtain ⟨n, hn⟩ := exists_norm_eq_zpow K v _ hx
    have hn' : ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ = qv ^ n := hn
    have hle : qv ^ n ≤ qv ^ (-(n₀ : ℤ)) := by
      rw [← hn', norm_sub_rev]; exact ht
    have hn₀ : n ≤ -(n₀ : ℤ) := (zpow_le_zpow_iff_right₀ hq1).mp hle
    refine ⟨(-n - n₀).toNat, ?_⟩
    show ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ = qv ^ (-(((-n - n₀).toNat + n₀ : ℕ) : ℤ))
    rw [hn']
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  ·
    intro k t ht τ hτ
    have ht1 : ‖(t : v.adicCompletion K)‖ = 1 := hsh_one k t ht
    have hsplit : (1 : v.adicCompletion K) - ((t * τ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        ((1 : v.adicCompletion K) - (t : v.adicCompletion K)) +
          (t : v.adicCompletion K) * ((1 : v.adicCompletion K) - (τ : v.adicCompletion K)) := by
      push_cast; ring
    have hlt : ‖(t : v.adicCompletion K) * ((1 : v.adicCompletion K) - (τ : v.adicCompletion K))‖ <
        ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ := by
      rw [norm_mul, ht1, one_mul, norm_sub_rev]
      show ‖(τ : v.adicCompletion K) - 1‖ < ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖
      rw [show ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ = qv ^ (-((k + n₀ : ℕ) : ℤ)) from ht]
      exact lt_of_le_of_lt hτ (zpow_lt_zpow_right₀ hq1 (by push_cast; omega))
    show ‖(1 : v.adicCompletion K) - ((t * τ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = qv ^ (-((k + n₀ : ℕ) : ℤ))
    rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt), max_eq_left hlt.le]
    exact ht
  ·
    intro k
    refine ⟨Ft k, ?_, hFt_sub k, hFt_ne k, hFt_cov k⟩

    have hs_mem : ∀ τ ∈ sh k, ‖(u ^ k * ((τ : v.adicCompletion K) - 1))‖ = qv ^ (-(n₀ : ℤ)) := by
      intro τ hτ
      rw [norm_mul, norm_pow, hu', hsh_norm k τ hτ, ← zpow_natCast, ← zpow_add₀ hq0.ne']
      congr 1; push_cast; ring
    have hs_ne : ∀ τ ∈ sh k, (1 : v.adicCompletion K) + u ^ k * ((τ : v.adicCompletion K) - 1) ≠ 0 := by
      intro τ hτ h0
      have h1 : ‖(1 : v.adicCompletion K) + u ^ k * ((τ : v.adicCompletion K) - 1)‖ = 1 := by
        apply norm_eq_one_of_norm_sub_one_lt K v
        rw [add_sub_cancel_left, hs_mem τ hτ]; exact hU1
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1

    let s : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ := fun τ =>
      if hτ : τ ∈ sh k then Units.mk0 _ (hs_ne τ hτ) else 1
    have hs_val : ∀ τ ∈ sh k, ((s τ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        1 + u ^ k * ((τ : v.adicCompletion K) - 1) := by
      intro τ hτ; simp [s, dif_pos hτ]
    have hs_sh : ∀ τ ∈ sh k, s τ ∈ sh 0 := by
      intro τ hτ
      show ‖(1 : v.adicCompletion K) - ((s τ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = qv ^ (-((0 + n₀ : ℕ) : ℤ))
      rw [hs_val τ hτ, norm_sub_rev, add_sub_cancel_left, hs_mem τ hτ]
      congr 1; push_cast; ring
    have hs_one : ∀ τ ∈ sh k, ‖((s τ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 :=
      fun τ hτ => hsh_one 0 _ (hs_sh τ hτ)
    have hs_diff : ∀ τ ∈ sh k, ∀ τ' ∈ sh k,
        ((s τ' : (v.adicCompletion K)ˣ) : v.adicCompletion K) - ((s τ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          u ^ k * ((τ' : v.adicCompletion K) - (τ : v.adicCompletion K)) := by
      intro τ hτ τ' hτ'; rw [hs_val τ hτ, hs_val τ' hτ']; ring

    have hρ : ∀ τ : (v.adicCompletion K)ˣ, ∃ ρ : (v.adicCompletion K)ˣ, τ ∈ sh k → ρ ∈ Ft 0 ∧ (s τ)⁻¹ * ρ ∈ V 0 := by
      intro τ
      by_cases hτ : τ ∈ sh k
      · obtain ⟨ρ, hρ, hmem⟩ := hFt_cov 0 (s τ) (hs_sh τ hτ)
        exact ⟨ρ, fun _ => ⟨hρ, hmem⟩⟩
      · exact ⟨1, fun h => absurd h hτ⟩
    choose ρ hρ using hρ
    refine Finset.card_le_card_of_injOn ρ (fun τ hτ => (hρ τ (hFt_sub k hτ)).1) ?_
    intro τ hτ τ' hτ' heq
    have hτs : τ ∈ sh k := hFt_sub k hτ
    have hτ's : τ' ∈ sh k := hFt_sub k hτ'
    by_contra hne
    apply hFt_ne k τ hτ τ' hτ' hne

    have h1 := (hρ τ hτs).2
    have h2 := (hρ τ' hτ's).2
    rw [heq] at h1
    have h12 : (s τ)⁻¹ * s τ' ∈ V 0 := by
      have := (V 0).mul_mem h1 ((V 0).inv_mem h2)
      simpa [mul_assoc] using this
    have hnorm : ‖((s τ' : (v.adicCompletion K)ˣ) : v.adicCompletion K) - ((s τ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤
        qv ^ (-((0 + n₀ + c : ℕ) : ℤ)) :=
      (inv_mul_mem_ballSub_iff K v (hV 0).1 (hV 0).2.2 (hs_one τ hτs)).mp h12
    rw [hs_diff τ hτs τ' hτ's, norm_mul, norm_pow, hu'] at hnorm

    have hτd : ‖(τ' : v.adicCompletion K) - (τ : v.adicCompletion K)‖ ≤ qv ^ (-((k + n₀ + c : ℕ) : ℤ)) := by
      have hqk : 0 < qv ^ k := pow_pos hq0 k
      refine le_of_mul_le_mul_left (hnorm.trans (le_of_eq ?_)) hqk
      rw [← zpow_natCast, ← zpow_add₀ hq0.ne']
      congr 1; push_cast; ring
    exact (inv_mul_mem_ballSub_iff K v (hV k).1 (hV k).2.2 (hsh_one k τ hτs)).mpr hτd
  ·
    intro S hS
    obtain ⟨R, -, hne, hcov⟩ := exists_finset_reps K v A (isOpen_ballSub K v hA0 hA0' hA1) S hS
    exact ⟨R, hne, hcov⟩

end S_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion (solution)
