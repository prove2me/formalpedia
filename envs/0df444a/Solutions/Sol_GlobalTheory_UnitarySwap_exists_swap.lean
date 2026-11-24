-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.exists_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:10.5365+00:00
-- url     : https://prove2.me/submissions/c708e621-3b2c-4339-b1b5-0ccfe0149b8f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_GlobalTheory_UnitarySwap_mul_lt_one
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_smul
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_pair
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_decomp
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_perp
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_inter
import Theorems.Thm_GlobalTheory_UnitarySwap_exists_refl
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}
variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution [FiniteDimensional L V] (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (hB : ∀ u v, σ (B u v) = B v u) {τ : L} (hτ : τ ∈ intL L) (hτ1 : τ + σ τ = 1) {ϖ : L}
    (hσϖ : σ ϖ = ϖ) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (m : ℕ) :
    ∀ (W : Submodule L V), Module.finrank L W < m → ∀ Λ Λ' : Set V, SelfDual B W Λ → SelfDual B W Λ' →
      (∃ N : ℕ, ∀ v ∈ Λ', ϖ ^ N • v ∈ Λ) →
      ∃ s : V →ₗ[L] V, (∀ u v, B (s u) (s v) = B u v) ∧ (∀ u, (∀ w ∈ W, B w u = 0) → s u = u) ∧
        (∀ v ∈ Λ, s v ∈ Λ') ∧ (∀ v ∈ Λ', s v ∈ Λ) := by
  classical
  have hσO : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by rw [mem_int, hσ]; exact hx
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  induction m with
  | zero => intro W hW; omega
  | succ m ih =>
  intro W hW Λ Λ' hΛ hΛ' hN
  have hback : ∀ N : ℕ, (∀ v ∈ Λ', ϖ ^ N • v ∈ Λ) → ∀ v ∈ Λ, ϖ ^ N • v ∈ Λ' := by
    intro N h v hv
    refine (hΛ' _).2 ⟨W.smul_mem _ ((hΛ v).1 hv).1, fun w hw => ?_⟩
    have := hΛ.pair hv (h w hw)
    simpa [map_smulₛₗ, hσϖ] using this
  have ha := Nat.find_spec hN
  rcases h0 : Nat.find hN with _ | b
  · rw [h0] at ha
    refine ⟨LinearMap.id, fun _ _ => rfl, fun _ _ => rfl, fun v hv => ?_, fun v hv => ?_⟩
    · simpa using hback 0 ha v hv
    · simpa using ha v hv
  have hb : ¬ ∀ v ∈ Λ', ϖ ^ b • v ∈ Λ := Nat.find_min hN (by omega)
  rw [h0] at ha
  push Not at hb
  obtain ⟨e, he, hne⟩ := hb
  have heW : e ∈ W := ((hΛ' e).1 he).1
  rw [hΛ] at hne
  push Not at hne
  obtain ⟨y, hy, hy'⟩ := hne (W.smul_mem _ heW)
  set π := ϖ ^ (b + 1) with hπdef
  have hπ0 : π ≠ 0 := pow_ne_zero _ hϖ0
  have hσπ : σ π = π := by rw [hπdef, map_pow, hσϖ]
  have hπ1 : Valued.v π < 1 := by
    rw [hπdef, map_pow]; exact pow_lt_one₀ zero_le hϖ1 (by omega)
  have hπO : π ∈ intL L := hπ1.le
  have hπe : π • e ∈ Λ := ha e he
  have hunit : Valued.v (π * B e y) = 1 := by
    have h1 : Valued.v (π * B e y) ≤ 1 := by
      have := hΛ.pair hπe hy
      simpa [map_smulₛₗ, hσπ, mem_int] using this
    refine le_antisymm h1 ?_
    have h2 : 1 < Valued.v (ϖ ^ b * B e y) := by
      rw [mem_int, not_le] at hy'
      simpa [map_smulₛₗ, hσϖ] using hy'
    have h3 : π * B e y = ϖ * (ϖ ^ b * B e y) := by rw [hπdef]; ring
    rw [h3, map_mul, hϖ]
    have h4 : Valued.v (ϖ ^ b * B e y) ≠ 0 := (lt_trans zero_lt_one h2).ne'
    rw [← WithZero.exp_log h4, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
    rw [← WithZero.exp_log h4, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hu0 : π * B e y ≠ 0 := by
    intro h; rw [h, map_zero] at hunit; exact zero_ne_one hunit
  have hey : B e y ≠ 0 := right_ne_zero_of_mul hu0
  obtain ⟨f, hf, hef⟩ : ∃ f ∈ Λ, B e f = π⁻¹ := by
    refine ⟨(π * B e y)⁻¹ • y, hΛ.smul hσO (by rw [mem_int, map_inv₀, hunit, inv_one]) hy, ?_⟩
    rw [map_smul, smul_eq_mul]; field_simp
  have hfe : B f e = π⁻¹ := by rw [← hB, hef, map_inv₀, hσπ]
  have hfW : f ∈ W := ((hΛ f).1 hf).1
  have hπf : π • f ∈ Λ' := hback _ ha f hf
  have hee := hΛ'.pair he he
  have hff := hΛ.pair hf hf
  have hsm : ∀ x v, B (π • x) v = π * B x v := by
    intro x v; simp [map_smulₛₗ, hσπ]
  have hsmall : Valued.v (π * (π * (B e e * B f f))) < 1 :=
    mul_lt_one hπ1 (mul_mem hπO (mul_mem hee hff))
  have hdec : ∀ v ∈ Λ, ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ,
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • (π • e) + d • f + v₀ := by
    intro v hv
    obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩ := hΛ.decomp hσO hπe hf
      (by rw [hsm, hef, mul_inv_cancel₀ hπ0]) (by rw [map_smul, hfe, smul_eq_mul, mul_inv_cancel₀ hπ0])
      (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv
    rw [hsm] at h1
    exact ⟨c, hc, d, hd, v₀, hv₀, (mul_eq_zero.1 h1).resolve_left hπ0, h2, h3⟩
  have hdec' : ∀ v ∈ Λ', ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ',
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • e + d • (π • f) + v₀ := by
    intro v hv
    obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, h3⟩ := hΛ'.decomp hσO he hπf
      (by rw [map_smul, hef, smul_eq_mul, mul_inv_cancel₀ hπ0]) (by rw [hsm, hfe, mul_inv_cancel₀ hπ0])
      (by convert hsmall using 2; rw [hsm, map_smul, smul_eq_mul]; ring) hv
    rw [hsm] at h2
    exact ⟨c, hc, d, hd, v₀, hv₀, h1, (mul_eq_zero.1 h2).resolve_left hπ0, h3⟩
  have hS := hΛ.inter hB (fun v h => by rw [hsm, h, mul_zero]) (fun v h => h) hdec
  have hS' := hΛ'.inter hB (fun v h => h) (fun v h => by rw [hsm, h, mul_zero]) hdec'
  have hlt : perp B W e f < W := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    rw [← h] at hfW
    exact inv_ne_zero hπ0 (hef ▸ (mem_perp.1 hfW).2.1)
  obtain ⟨s₀, i₀, f₀, m₀, m₀'⟩ := ih (perp B W e f)
    (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega) _ _ hS hS'
    ⟨b + 1, fun v hv => ⟨ha v hv.1, (perp B W e f).smul_mem _ hv.2⟩⟩
  obtain ⟨s₁, i₁, f₁, r, hr, r', hr', se, sf⟩ := exists_refl hB hτ hτ1 hπ0 hπ1 hσπ hef hee hff
  have s₀e : s₀ e = e := f₀ e fun w hw => by rw [← hB, (mem_perp.1 hw).2.1, map_zero]
  have s₀f : s₀ f = f := f₀ f fun w hw => by rw [← hB, (mem_perp.1 hw).2.2, map_zero]
  have h1r : 1 + π * r ∈ intL L := add_mem (one_mem _) (mul_mem hπO hr)
  have h1r' : 1 + π * r' ∈ intL L := add_mem (one_mem _) (mul_mem hπO hr')
  refine ⟨s₁ ∘ₗ s₀, fun u v => ?_, fun u hu => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · simp only [LinearMap.comp_apply, i₁, i₀]
  · rw [LinearMap.comp_apply, f₀ u fun w hw => hu w (mem_perp.1 hw).1, f₁ u (hu e heW) (hu f hfW)]
  · obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, rfl⟩ := hdec v hv
    have h3 := m₀ v₀ ⟨hv₀, mem_perp.2 ⟨((hΛ v₀).1 hv₀).1, h1, h2⟩⟩
    have h4 := mem_perp.1 h3.2
    have : (s₁ ∘ₗ s₀) (c • (π • e) + d • f + v₀) =
        (c * (-r * π * π) + d * (1 + π * r')) • e + (c * (1 + π * r) + d * (-r')) • (π • f) + s₀ v₀ := by
      simp only [LinearMap.comp_apply, map_add, map_smul, s₀e, s₀f, f₁ _ h4.2.1 h4.2.2, se, sf]
      module
    rw [this]
    refine hΛ'.add (hΛ'.add (hΛ'.smul hσO ?_ he) (hΛ'.smul hσO ?_ hπf)) h3.1
    · exact add_mem (mul_mem hc (mul_mem (mul_mem (neg_mem hr) hπO) hπO)) (mul_mem hd h1r')
    · exact add_mem (mul_mem hc h1r) (mul_mem hd (neg_mem hr'))
  · obtain ⟨c, hc, d, hd, v₀, hv₀, h1, h2, rfl⟩ := hdec' v hv
    have h3 := m₀' v₀ ⟨hv₀, mem_perp.2 ⟨((hΛ' v₀).1 hv₀).1, h1, h2⟩⟩
    have h4 := mem_perp.1 h3.2
    have : (s₁ ∘ₗ s₀) (c • e + d • (π • f) + v₀) =
        (c * (-r) + d * (1 + π * r')) • (π • e) + (c * (1 + π * r) + d * (-r' * π * π)) • f + s₀ v₀ := by
      simp only [LinearMap.comp_apply, map_add, map_smul, s₀e, s₀f, f₁ _ h4.2.1 h4.2.2, se, sf]
      module
    rw [this]
    refine hΛ.add (hΛ.add (hΛ.smul hσO ?_ hπe) (hΛ.smul hσO ?_ hf)) h3.1
    · exact add_mem (mul_mem hc (neg_mem hr)) (mul_mem hd h1r')
    · exact add_mem (mul_mem hc h1r) (mul_mem hd (mul_mem (mul_mem (neg_mem hr') hπO) hπO))
end GlobalTheory.UnitarySwap
