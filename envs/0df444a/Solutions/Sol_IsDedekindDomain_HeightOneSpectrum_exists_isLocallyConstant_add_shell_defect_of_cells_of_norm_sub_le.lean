-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/411ba21f-0056-5cf1-8e90-2d7b727c22df

import Mathlib
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le

set_option autoImplicit false

open IsDedekindDomain NumberField

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Ψ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ)
    (hcs : HasCompactSupport Ψ)
    (hlc : ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Ψ q = Ψ p)
    (hcells : ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
          Ψ (a', t') = Ψ (a, t))
    (hgerm : ∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
      ‖Ψ (a, t) - Ψ (a, 1)‖ ≤ C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ *
        (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) :
    ∃ (Ψ₀ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ), IsLocallyConstant Ψ₀ ∧ HasCompactSupport Ψ₀ ∧
    ∃ (U₁ A : Subgroup (v.adicCompletion K)ˣ), IsOpen (U₁ : Set (v.adicCompletion K)ˣ) ∧ IsOpen (A : Set (v.adicCompletion K)ˣ) ∧ IsCompact (A : Set (v.adicCompletion K)ˣ) ∧
    ∃ (V : ℕ → Subgroup (v.adicCompletion K)ˣ), (∀ k, IsOpen (V k : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, V k ≤ U₁) ∧ (∀ k, V k ≤ A) ∧
    ∃ (sh : ℕ → Set (v.adicCompletion K)ˣ),
      (∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, IsCompact (sh k)) ∧ (∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh k) ∧
      (Pairwise fun k k' => Disjoint (sh k) (sh k')) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ≠ 1 → ∃ k, t ∈ sh k) ∧
      (∀ k, ∀ t ∈ sh k, ∀ τ ∈ V k, t * τ ∈ sh k) ∧
    ∃ (Fa : Finset (v.adicCompletion K)ˣ), (∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A) ∧
    ∃ (M₀ : ℕ) (C' : ℝ), 0 ≤ C' ∧
      (∀ a t : (v.adicCompletion K)ˣ, (∀ k, t ∉ sh k) → Ψ (a, t) = Ψ₀ (a, t)) ∧
      (∀ k, ∃ (Ft : Finset (v.adicCompletion K)ˣ) (c : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ), Ft.card ≤ M₀ ∧
        (∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V k) ∧
        (∀ α τ, ‖c α τ‖ ≤ C' * ((k : ℝ) + 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ))) ∧
        ∀ a t : (v.adicCompletion K)ˣ, t ∈ sh k →
          Ψ (a, t) = Ψ₀ (a, t) +
            ∑ α ∈ Fa, ∑ τ ∈ Ft, c α τ * (if a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k then 1 else 0)) := by
  classical
  obtain ⟨U, hU, ρ, hρ, hcell⟩ := hcells
  obtain ⟨C, hC⟩ := hgerm
  set qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqv
  have hq1 : 1 < qv := by rw [hqv]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : 0 < qv := one_pos.trans hq1

  have hUval : ∃ ε : ℝ, 0 < ε ∧ ∀ t : (v.adicCompletion K)ˣ, ‖(t : (v.adicCompletion K)) - 1‖ < ε → t ∈ U := by
    have hind := Units.isOpenEmbedding_val (R := (v.adicCompletion K)) |>.isEmbedding.isInducing
    rw [hind.nhds_eq_comap, Filter.mem_comap] at hU
    obtain ⟨W, hW, hWU⟩ := hU
    rw [Units.val_one] at hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
    refine ⟨ε, hε, fun t ht => hWU (hball ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]; exact ht
  obtain ⟨ε, hε, hεU⟩ := hUval
  have hqinv : qv⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hqinv0 : 0 < qv⁻¹ := inv_pos.mpr hq0
  obtain ⟨n₁, hn₁⟩ := exists_pow_lt_of_lt_one hε hqinv
  obtain ⟨c₁, hc₁⟩ := exists_pow_lt_of_lt_one hρ hqinv
  set n₀ : ℕ := n₁ + 1 with hn₀
  set c : ℕ := c₁ + 1 with hcdef
  have hzpow : ∀ m : ℕ, qv ^ (-(m : ℤ)) = qv⁻¹ ^ m := fun m => by rw [zpow_neg, zpow_natCast, inv_pow]
  have hn₀ε : qv ^ (-(n₀ : ℤ)) < ε := by
    rw [hzpow]; exact lt_of_le_of_lt (pow_le_pow_of_le_one hqinv0.le hqinv.le (by omega)) hn₁
  have hcρ : qv ^ (-(c : ℤ)) ≤ ρ := by
    rw [hzpow]; exact (pow_le_pow_of_le_one hqinv0.le hqinv.le (by omega)).trans hc₁.le

  obtain ⟨U₁, A, V, sh, M₀, hU₁o, hU₁c, hAo, hAc, hVo, hVU, hVA, hU₁mem, hAmem, hVmem, hshmem, hU₁one, hshc, hshU,
    hsh1, hshdis, hshcov, hshst, hFt, hFaS⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_subgroups_shells_finset_card_le_of_units_adicCompletion K v n₀ c
      (by omega) (by omega)
  have hU₁U : ∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ∈ U := fun t ht => hεU t (lt_of_le_of_lt ((hU₁mem t).mp ht) hn₀ε)
  have h1U : (1 : (v.adicCompletion K)ˣ) ∈ U := hU₁U 1 U₁.one_mem

  have hcellA : ∀ a α t : (v.adicCompletion K)ˣ, a⁻¹ * α ∈ A → t ∈ U → Ψ (α, t) = Ψ (a, t) := by
    intro a α t hα ht
    refine hcell a α t t ht ?_ (by rw [sub_self, norm_zero]; positivity)
    have hn : ‖((a⁻¹ * α : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) - 1‖ ≤ qv ^ (-(c : ℤ)) := (hAmem _).mp hα
    have : (α : (v.adicCompletion K)) - (a : (v.adicCompletion K)) = (a : (v.adicCompletion K)) * (((a⁻¹ * α : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) - 1) := by
      rw [mul_sub, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul, mul_one]
    rw [this, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hn.trans hcρ) (norm_nonneg _)
  have hcellV : ∀ (k : ℕ) (a t τ : (v.adicCompletion K)ˣ), t ∈ sh k → t⁻¹ * τ ∈ V k → Ψ (a, τ) = Ψ (a, t) := by
    intro k a t τ ht hτ
    refine hcell a a t τ (hU₁U t (hshU k ht)) (by simp [hρ.le]) ?_
    have ht1 : ‖(t : (v.adicCompletion K))‖ = 1 := hU₁one t (hshU k ht)
    have hn : ‖((t⁻¹ * τ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) - 1‖ ≤ qv ^ (-((k + n₀ + c : ℕ) : ℤ)) := (hVmem k _).mp hτ
    have : (τ : (v.adicCompletion K)) - (t : (v.adicCompletion K)) = (t : (v.adicCompletion K)) * (((t⁻¹ * τ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) - 1) := by
      rw [mul_sub, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul, mul_one]
    rw [this, norm_mul, ht1, one_mul]
    refine hn.trans ?_
    rw [(hshmem k t).mp ht]
    have : qv ^ (-((k + n₀ + c : ℕ) : ℤ)) = qv ^ (-(c : ℤ)) * qv ^ (-((k + n₀ : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hq0.ne']; congr 1; push_cast; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hcρ (zpow_pos hq0 _).le

  let Ψ₀ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ := fun p => if p.2 ∈ U₁ then Ψ (p.1, 1) else Ψ p
  have hΨ₀U : ∀ a t : (v.adicCompletion K)ˣ, t ∈ U₁ → Ψ₀ (a, t) = Ψ (a, 1) := fun a t ht => if_pos ht
  have hΨ₀nU : ∀ a t : (v.adicCompletion K)ˣ, t ∉ U₁ → Ψ₀ (a, t) = Ψ (a, t) := fun a t ht => if_neg ht
  have hU₁closed : IsClosed (U₁ : Set (v.adicCompletion K)ˣ) := hU₁c.isClosed
  have hΨ₀lc : IsLocallyConstant Ψ₀ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨a, t⟩
    by_cases ht : t ∈ U₁
    ·
      have hρa : 0 < ρ * ‖(a : (v.adicCompletion K))‖ := mul_pos hρ (norm_pos_iff.mpr a.ne_zero)
      have hO : IsOpen (((fun p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ => ((p.1 : (v.adicCompletion K)ˣ) : (v.adicCompletion K))) ⁻¹' Metric.ball (a : (v.adicCompletion K)) (ρ * ‖(a : (v.adicCompletion K))‖)) ∩
          (Prod.snd ⁻¹' (U₁ : Set (v.adicCompletion K)ˣ))) :=
        (Metric.isOpen_ball.preimage (Units.continuous_val.comp continuous_fst)).inter (hU₁o.preimage continuous_snd)
      refine Filter.eventually_of_mem (hO.mem_nhds ⟨Metric.mem_ball_self hρa, ht⟩) fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : ‖((p.1 : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ < ρ * ‖(a : (v.adicCompletion K))‖ := by
        rw [← dist_eq_norm]; exact hp1
      show Ψ₀ (p.1, p.2) = Ψ₀ (a, t)
      rw [hΨ₀U p.1 p.2 hp2, hΨ₀U a t ht]
      exact hcell a p.1 1 1 h1U hp1'.le (by simp)
    · have ht1 : t ≠ 1 := fun h => ht (h ▸ U₁.one_mem)
      obtain ⟨W, hW, hWc⟩ := hlc (a, t) ht1
      have hO : IsOpen {p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ | p.2 ∉ U₁} := hU₁closed.isOpen_compl.preimage continuous_snd
      refine Filter.eventually_of_mem (Filter.inter_mem hW (hO.mem_nhds ht)) fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := hp
      show Ψ₀ (p.1, p.2) = Ψ₀ (a, t)
      rw [hΨ₀nU p.1 p.2 hp2, hΨ₀nU a t ht]
      exact hWc p hp1

  set K₀ := tsupport Ψ with hK₀
  have hK₀c : IsCompact K₀ := hcs
  set Ka : Set (v.adicCompletion K)ˣ := Prod.fst '' K₀ with hKa
  have hKac : IsCompact Ka := hK₀c.image continuous_fst
  have hΨ0 : ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.1 ∉ Ka → Ψ p = 0 := by
    intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hp ⟨p, h, rfl⟩
  have hΨ₀cs : HasCompactSupport Ψ₀ := by
    refine HasCompactSupport.intro ((hKac.prod hU₁c).union hK₀c) fun p hp => ?_
    by_cases h2 : p.2 ∈ U₁
    · show Ψ₀ (p.1, p.2) = 0
      rw [hΨ₀U p.1 p.2 h2]
      have h1 : p.1 ∉ Ka := fun h => hp (Or.inl ⟨h, h2⟩)
      exact hΨ0 (p.1, 1) h1
    · show Ψ₀ (p.1, p.2) = 0
      rw [hΨ₀nU p.1 p.2 h2]
      exact image_eq_zero_of_notMem_tsupport fun h => hp (Or.inr h)

  obtain ⟨Fa, hFane, hFacov⟩ := hFaS Ka hKac

  set L : ℝ := Real.log qv with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hq1.le
  set C' : ℝ := max C 0 * qv ^ (-(n₀ : ℤ)) * (1 + ((n₀ : ℝ) + 1) * L) with hC'
  have hC'0 : 0 ≤ C' := by
    rw [hC']; refine mul_nonneg (mul_nonneg (le_max_right _ _) (zpow_pos hq0 _).le) ?_; positivity
  have hbound : ∀ (k : ℕ) (α τ : (v.adicCompletion K)ˣ), τ ∈ sh k →
      ‖Ψ (α, τ) - Ψ (α, 1)‖ ≤ C' * ((k : ℝ) + 1) * qv ^ (-(k : ℤ)) := by
    intro k α τ hτ
    have hnorm : ‖(1 : (v.adicCompletion K)) - (τ : (v.adicCompletion K))‖ = qv ^ (-((k + n₀ : ℕ) : ℤ)) := (hshmem k τ).mp hτ
    have h1 := hC α τ
    rw [hnorm] at h1
    have hlog : |Real.log (qv ^ (-((k + n₀ : ℕ) : ℤ)))| = ((k : ℝ) + n₀) * L := by
      rw [Real.log_zpow, abs_mul, abs_of_nonneg hL0]
      congr 1
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [hlog] at h1
    refine h1.trans ?_
    have hsplit : qv ^ (-((k + n₀ : ℕ) : ℤ)) = qv ^ (-(n₀ : ℤ)) * qv ^ (-(k : ℤ)) := by
      rw [← zpow_add₀ hq0.ne']; congr 1; push_cast; ring
    rw [hsplit, hC']
    have hX : 0 ≤ qv ^ (-(n₀ : ℤ)) * qv ^ (-(k : ℤ)) * (1 + ((k : ℝ) + n₀) * L) := by positivity
    calc C * (qv ^ (-(n₀ : ℤ)) * qv ^ (-(k : ℤ))) * (1 + ((k : ℝ) + n₀) * L)
        = C * (qv ^ (-(n₀ : ℤ)) * qv ^ (-(k : ℤ)) * (1 + ((k : ℝ) + n₀) * L)) := by ring
      _ ≤ max C 0 * (qv ^ (-(n₀ : ℤ)) * qv ^ (-(k : ℤ)) * (1 + ((k : ℝ) + n₀) * L)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX
      _ ≤ max C 0 * (qv ^ (-(n₀ : ℤ)) * qv ^ (-(k : ℤ)) * (((k : ℝ) + 1) * (1 + ((n₀ : ℝ) + 1) * L))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (le_max_right _ _)
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
          nlinarith [mul_nonneg (mul_nonneg hk hn) hL0, hL0, hk]
      _ = max C 0 * qv ^ (-(n₀ : ℤ)) * (1 + ((n₀ : ℝ) + 1) * L) * ((k : ℝ) + 1) * qv ^ (-(k : ℤ)) := by ring

  refine ⟨Ψ₀, hΨ₀lc, hΨ₀cs, U₁, A, hU₁o, hAo, hAc, V, hVo, hVU, hVA, sh, hshU, hshc, hsh1, hshdis, hshcov, hshst,
    Fa, hFane, M₀, C', hC'0, ?_, ?_⟩
  ·
    intro a t ht
    by_cases htU : t ∈ U₁
    · have ht1 : t = 1 := by
        by_contra hne
        obtain ⟨k, hk⟩ := hshcov t htU hne
        exact ht k hk
      rw [hΨ₀U a t htU, ht1]
    · rw [hΨ₀nU a t htU]
  · intro k
    obtain ⟨Ft, hcard, hFtsh, hFtne, hFtcov⟩ := hFt k
    refine ⟨Ft, fun α τ => if τ ∈ sh k then Ψ (α, τ) - Ψ (α, 1) else 0, hcard, hFtne, ?_, ?_⟩
    · intro α τ
      show ‖(if τ ∈ sh k then Ψ (α, τ) - Ψ (α, 1) else 0)‖ ≤ C' * ((k : ℝ) + 1) * qv ^ (-(k : ℤ))
      by_cases hτ : τ ∈ sh k
      · rw [if_pos hτ]; exact hbound k α τ hτ
      · rw [if_neg hτ, norm_zero]; positivity
    · intro a t ht
      rw [hΨ₀U a t (hshU k ht)]
      by_cases ha : ∃ α ∈ Fa, a⁻¹ * α ∈ A
      · obtain ⟨α₀, hα₀, hα₀A⟩ := ha
        obtain ⟨τ₀, hτ₀, hτ₀V⟩ := hFtcov t ht
        have hτ₀sh : τ₀ ∈ sh k := hFtsh hτ₀

        have hsum : (∑ α ∈ Fa, ∑ τ ∈ Ft, (if τ ∈ sh k then Ψ (α, τ) - Ψ (α, 1) else 0) *
            (if a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k then (1 : ℂ) else 0)) = Ψ (α₀, τ₀) - Ψ (α₀, 1) := by
          rw [Finset.sum_eq_single_of_mem α₀ hα₀]
          · rw [Finset.sum_eq_single_of_mem τ₀ hτ₀]
            · rw [if_pos hτ₀sh, if_pos ⟨hα₀A, hτ₀V⟩, mul_one]
            · intro τ hτ hne
              have : ¬ (a⁻¹ * α₀ ∈ A ∧ t⁻¹ * τ ∈ V k) := by
                rintro ⟨-, hτV⟩
                apply hFtne τ₀ hτ₀ τ hτ (Ne.symm hne)
                have := (V k).mul_mem ((V k).inv_mem hτ₀V) hτV
                simpa [mul_assoc] using this
              rw [if_neg this, mul_zero]
          · intro α hα hne
            refine Finset.sum_eq_zero fun τ _ => ?_
            have : ¬ (a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k) := by
              rintro ⟨hαA, -⟩
              apply hFane α₀ hα₀ α hα (Ne.symm hne)
              have := A.mul_mem (A.inv_mem hα₀A) hαA
              simpa [mul_assoc] using this
            rw [if_neg this, mul_zero]
        rw [hsum]

        have h1 : Ψ (α₀, τ₀) = Ψ (a, t) := by
          rw [hcellA a α₀ τ₀ hα₀A (hU₁U τ₀ (hshU k hτ₀sh))]
          exact hcellV k a t τ₀ ht hτ₀V
        have h2 : Ψ (α₀, 1) = Ψ (a, 1) := hcellA a α₀ 1 hα₀A h1U
        rw [h1, h2]; ring
      ·
        push Not at ha
        have haK : a ∉ Ka := fun h => by
          obtain ⟨α, hα, hαA⟩ := hFacov a h
          exact ha α hα hαA
        have hsum : (∑ α ∈ Fa, ∑ τ ∈ Ft, (if τ ∈ sh k then Ψ (α, τ) - Ψ (α, 1) else 0) *
            (if a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k then (1 : ℂ) else 0)) = 0 := by
          refine Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun τ _ => ?_
          have : ¬ (a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k) := fun h => ha α hα h.1
          rw [if_neg this, mul_zero]
        rw [hsum, hΨ0 (a, t) haK, hΨ0 (a, 1) haK, add_zero]

end S_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le (solution)
