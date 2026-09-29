-- Prove2me | solution 1 for InnerProductSpace.exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cdcf1e36-bac5-5e15-aecf-a0c693cc69a0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace CyclicLevelAverageEngine

structure Setup (G : Type*) [Group G] (L : Type*) [AddCommGroup L] [Module ℂ L]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  ρ : G →* (L →ₗ[ℂ] L)
  S : Submodule ℂ L
  hS : ∀ x : G, ∀ f ∈ S, ρ x f ∈ S
  ι : L → H
  hι : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → ι (a • f + b • g) = a • ι f + b • ι g
  c : G → ℝ
  hc : ∀ x, 0 < c x
  hρ : ∀ x : G, ∀ f ∈ S, ‖ι (ρ x f)‖ ^ 2 = c x * ‖ι f‖ ^ 2
  P : L → Prop
  E : L → L
  hE : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → E (a • f + b • g) = a • E f + b • E g
  hEP : ∀ f ∈ S, P (E f)
  hEinner : ∀ f ∈ S, ∀ g ∈ S, P g → ⟪ι (E f), ι g⟫_ℂ = ⟪ι f, ι g⟫_ℂ
  φ : L
  φ' : L
  hφ : φ ∈ S
  hPφ : P φ
  hφ' : φ' ∈ S
  hspan : ∀ ε : ℝ, 0 < ε →
    ∃ v ∈ Submodule.span ℂ (Set.range fun x : G => ρ x φ), ‖ι φ' - ι v‖ < ε
  W : Submodule ℂ L
  hWS : W ≤ S
  hWφ' : W ≤ Submodule.span ℂ (Set.range fun x : G => ρ x φ')
  hWρ : ∀ x : G, ∀ w ∈ W, ρ x w ∈ W
  hWE : ∀ w ∈ W, E w ∈ W
  hEφ' : ∀ x : G, E (ρ x φ') ∈ W

variable {G : Type*} [Group G] {L : Type*} [AddCommGroup L] [Module ℂ L]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Setup G L H)

namespace Setup

theorem ι_add {f g : L} (hf : f ∈ X.S) (hg : g ∈ X.S) : X.ι (f + g) = X.ι f + X.ι g := by
  simpa using X.hι 1 1 f g hf hg

theorem ι_sub {f g : L} (hf : f ∈ X.S) (hg : g ∈ X.S) : X.ι (f - g) = X.ι f - X.ι g := by
  have h := X.hι 1 (-1) f g hf hg
  simp only [one_smul, neg_smul, one_smul] at h
  rw [sub_eq_add_neg, h, sub_eq_add_neg]

theorem ι_smul (a : ℂ) {f : L} (hf : f ∈ X.S) : X.ι (a • f) = a • X.ι f := by
  have h := X.hι a 0 f f hf hf
  simpa using h

theorem ι_zero : X.ι 0 = 0 := by
  have h := X.hι 0 0 0 0 X.S.zero_mem X.S.zero_mem
  simpa using h

theorem E_sub {f g : L} (hf : f ∈ X.S) (hg : g ∈ X.S) : X.E (f - g) = X.E f - X.E g := by
  have h := X.hE 1 (-1) f g hf hg
  simp only [one_smul, neg_smul, one_smul] at h
  rw [sub_eq_add_neg, h, sub_eq_add_neg]

theorem ρ_mul_apply (x y : G) (f : L) : X.ρ (x * y) f = X.ρ x (X.ρ y f) := by
  rw [map_mul]; rfl

theorem ρ_inv_apply (x : G) (f : L) : X.ρ x (X.ρ x⁻¹ f) = f := by
  rw [← ρ_mul_apply, mul_inv_cancel, map_one]; rfl

theorem ρ_inv_apply' (x : G) (f : L) : X.ρ x⁻¹ (X.ρ x f) = f := by
  rw [← ρ_mul_apply, inv_mul_cancel, map_one]; rfl

theorem norm_ι_ρ (x : G) {f : L} (hf : f ∈ X.S) :
    ‖X.ι (X.ρ x f)‖ = Real.sqrt (X.c x) * ‖X.ι f‖ := by
  have h := X.hρ x f hf
  have h1 : ‖X.ι (X.ρ x f)‖ = Real.sqrt (‖X.ι (X.ρ x f)‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _)]
  rw [h1, h, Real.sqrt_mul (X.hc x).le, Real.sqrt_sq (norm_nonneg _)]

theorem inner_ι_ρ (x : G) {f g : L} (hf : f ∈ X.S) (hg : g ∈ X.S) :
    ⟪X.ι (X.ρ x f), X.ι (X.ρ x g)⟫_ℂ = (X.c x : ℂ) * ⟪X.ι f, X.ι g⟫_ℂ := by
  have key : ∀ (a : ℂ), ‖X.ι (X.ρ x f) + a • X.ι (X.ρ x g)‖ ^ 2
      = X.c x * ‖X.ι f + a • X.ι g‖ ^ 2 := by
    intro a
    have hmem : f + a • g ∈ X.S := X.S.add_mem hf (X.S.smul_mem a hg)
    have h1 : X.ι (X.ρ x f) + a • X.ι (X.ρ x g) = X.ι (X.ρ x (f + a • g)) := by
      rw [map_add, map_smul, X.ι_add (X.hS x f hf) (X.S.smul_mem a (X.hS x g hg)),
        X.ι_smul a (X.hS x g hg)]
    have h2 : X.ι f + a • X.ι g = X.ι (f + a • g) := by
      rw [X.ι_add hf (X.S.smul_mem a hg), X.ι_smul a hg]
    rw [h1, h2, X.hρ x _ hmem]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-RCLike.I)
  have k4 := key (RCLike.I)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  apply Complex.ext
  · have h1 := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)
      (X.ι (X.ρ x f)) (X.ι (X.ρ x g))
    have h2 := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)
      (X.ι f) (X.ι g)
    simp only [RCLike.re_to_complex] at h1 h2
    rw [Complex.re_ofReal_mul, h1, h2]
    linear_combination (k1 - k2) / 4
  · have h1 := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
      (𝕜 := ℂ) (X.ι (X.ρ x f)) (X.ι (X.ρ x g))
    have h2 := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
      (𝕜 := ℂ) (X.ι f) (X.ι g)
    simp only [RCLike.im_to_complex] at h1 h2
    rw [Complex.im_ofReal_mul, h1, h2]
    linear_combination (k3 - k4) / 4

def V (ψ : L) : Submodule ℂ L := Submodule.span ℂ (Set.range fun x : G => X.ρ x ψ)

theorem ρ_mem_V (x : G) (ψ : L) : X.ρ x ψ ∈ X.V ψ := Submodule.subset_span ⟨x, rfl⟩

theorem self_mem_V (ψ : L) : ψ ∈ X.V ψ := by
  have h := X.ρ_mem_V 1 ψ
  rwa [map_one] at h

theorem V_le_S {ψ : L} (hψ : ψ ∈ X.S) : X.V ψ ≤ X.S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, rfl⟩
  exact X.hS x ψ hψ

theorem ρ_mem_V_of_mem (y : G) {ψ v : L} (hv : v ∈ X.V ψ) : X.ρ y v ∈ X.V ψ := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    rw [← ρ_mul_apply]
    exact X.ρ_mem_V _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | smul a u _ hu => rw [map_smul]; exact Submodule.smul_mem _ a hu

def Approx (ψ : L) : Prop := ∀ ε : ℝ, 0 < ε → ∃ v ∈ X.V X.φ, ‖X.ι ψ - X.ι v‖ < ε

theorem approx_φ' : X.Approx X.φ' := X.hspan

theorem approx_ρ (y : G) {ψ : L} (hψ : ψ ∈ X.S) (h : X.Approx ψ) : X.Approx (X.ρ y ψ) := by
  intro ε hε
  have hs : 0 < Real.sqrt (X.c y) := Real.sqrt_pos.mpr (X.hc y)
  obtain ⟨v, hv, hlt⟩ := h (ε / Real.sqrt (X.c y)) (div_pos hε hs)
  refine ⟨X.ρ y v, X.ρ_mem_V_of_mem y hv, ?_⟩
  have hvS : v ∈ X.S := X.V_le_S X.hφ hv
  rw [← X.ι_sub (X.hS y ψ hψ) (X.hS y v hvS), ← map_sub, X.norm_ι_ρ y (X.S.sub_mem hψ hvS),
    X.ι_sub hψ hvS]
  rwa [lt_div_iff₀ hs, mul_comm] at hlt

theorem approx_add {ψ₁ ψ₂ : L} (h₁S : ψ₁ ∈ X.S) (h₂S : ψ₂ ∈ X.S) (h₁ : X.Approx ψ₁)
    (h₂ : X.Approx ψ₂) : X.Approx (ψ₁ + ψ₂) := by
  intro ε hε
  obtain ⟨v₁, hv₁, hlt₁⟩ := h₁ (ε / 2) (by positivity)
  obtain ⟨v₂, hv₂, hlt₂⟩ := h₂ (ε / 2) (by positivity)
  refine ⟨v₁ + v₂, Submodule.add_mem _ hv₁ hv₂, ?_⟩
  have hv₁S := X.V_le_S X.hφ hv₁
  have hv₂S := X.V_le_S X.hφ hv₂
  rw [X.ι_add h₁S h₂S, X.ι_add hv₁S hv₂S]
  calc ‖X.ι ψ₁ + X.ι ψ₂ - (X.ι v₁ + X.ι v₂)‖
      = ‖(X.ι ψ₁ - X.ι v₁) + (X.ι ψ₂ - X.ι v₂)‖ := by congr 1; abel
    _ ≤ ‖X.ι ψ₁ - X.ι v₁‖ + ‖X.ι ψ₂ - X.ι v₂‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hlt₁ hlt₂
    _ = ε := by ring

theorem approx_smul (a : ℂ) {ψ : L} (hψS : ψ ∈ X.S) (h : X.Approx ψ) : X.Approx (a • ψ) := by
  intro ε hε
  have hpos : 0 < ‖a‖ + 1 := by positivity
  obtain ⟨v, hv, hlt⟩ := h (ε / (‖a‖ + 1)) (div_pos hε hpos)
  refine ⟨a • v, Submodule.smul_mem _ a hv, ?_⟩
  have hvS := X.V_le_S X.hφ hv
  rw [X.ι_smul a hψS, X.ι_smul a hvS, ← smul_sub, norm_smul]
  calc ‖a‖ * ‖X.ι ψ - X.ι v‖ ≤ (‖a‖ + 1) * ‖X.ι ψ - X.ι v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (‖a‖ + 1) * (ε / (‖a‖ + 1)) := mul_lt_mul_of_pos_left hlt hpos
    _ = ε := mul_div_cancel₀ ε hpos.ne'

theorem approx_zero : X.Approx 0 := by
  intro ε hε
  exact ⟨0, Submodule.zero_mem _, by simpa [X.ι_zero] using hε⟩

theorem approx_sub {ψ₁ ψ₂ : L} (h₁S : ψ₁ ∈ X.S) (h₂S : ψ₂ ∈ X.S) (h₁ : X.Approx ψ₁)
    (h₂ : X.Approx ψ₂) : X.Approx (ψ₁ - ψ₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ₂]
  exact X.approx_add h₁S (X.S.smul_mem _ h₂S) h₁ (X.approx_smul _ h₂S h₂)

theorem approx_of_mem_V' {w : L} (hw : w ∈ X.V X.φ') : X.Approx w := by
  induction hw using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, rfl⟩ := hu
    exact X.approx_ρ x X.hφ' X.approx_φ'
  | zero => exact X.approx_zero
  | add u u' hu hu' ihu ihu' =>
    exact X.approx_add (X.V_le_S X.hφ' hu) (X.V_le_S X.hφ' hu') ihu ihu'
  | smul a u hu ihu => exact X.approx_smul a (X.V_le_S X.hφ' hu) ihu

theorem approx_of_mem_W {w : L} (hw : w ∈ X.W) : X.Approx w := X.approx_of_mem_V' (X.hWφ' hw)

def d (w : X.W) : ℝ := ‖X.ι X.φ' - X.ι (w : L)‖

def δ : ℝ := ⨅ w : X.W, X.d w

theorem d_nonneg (w : X.W) : 0 ≤ X.d w := norm_nonneg _

theorem bddBelow_d : BddBelow (Set.range X.d) := ⟨0, by rintro _ ⟨w, rfl⟩; exact X.d_nonneg w⟩

scoped instance : Nonempty X.W := ⟨0⟩

theorem δ_le (w : X.W) : X.δ ≤ X.d w := ciInf_le X.bddBelow_d w

theorem δ_nonneg : 0 ≤ X.δ := le_ciInf fun w => X.d_nonneg w

theorem exists_d_lt (η : ℝ) (hη : 0 < η) : ∃ w : X.W, X.d w < X.δ + η :=
  exists_lt_of_ciInf_lt (by show iInf X.d < iInf X.d + η; linarith)

theorem δ_le_of_mem {w : L} (hw : w ∈ X.W) : X.δ ≤ ‖X.ι X.φ' - X.ι w‖ := X.δ_le ⟨w, hw⟩

def wseq (n : ℕ) : X.W := (X.exists_d_lt (1 / ((n : ℝ) + 1)) (by positivity)).choose

theorem d_wseq_lt (n : ℕ) : X.d (X.wseq n) < X.δ + 1 / ((n : ℝ) + 1) :=
  (X.exists_d_lt (1 / ((n : ℝ) + 1)) (by positivity)).choose_spec

def ψ (n : ℕ) : L := X.φ' - (X.wseq n : L)

theorem wseq_mem (n : ℕ) : (X.wseq n : L) ∈ X.W := (X.wseq n).2

theorem wseq_memS (n : ℕ) : (X.wseq n : L) ∈ X.S := X.hWS (X.wseq_mem n)

theorem ψ_memS (n : ℕ) : X.ψ n ∈ X.S := X.S.sub_mem X.hφ' (X.wseq_memS n)

theorem ι_ψ (n : ℕ) : X.ι (X.ψ n) = X.ι X.φ' - X.ι (X.wseq n : L) :=
  X.ι_sub X.hφ' (X.wseq_memS n)

theorem norm_ι_ψ (n : ℕ) : ‖X.ι (X.ψ n)‖ = X.d (X.wseq n) := by rw [X.ι_ψ]; rfl

def K₀ : ℝ := 2 * X.δ + 1

theorem K₀_pos : 0 < X.K₀ := by have := X.δ_nonneg; unfold K₀; linarith

theorem sq_norm_ι_ψ_sub_le (n : ℕ) :
    ‖X.ι (X.ψ n)‖ ^ 2 - X.δ ^ 2 ≤ X.K₀ / ((n : ℝ) + 1) := by
  rw [X.norm_ι_ψ]
  have h1 := X.d_wseq_lt n
  have h0 := X.d_nonneg (X.wseq n)
  have hδ := X.δ_nonneg
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsq : X.d (X.wseq n) ^ 2 < (X.δ + 1 / ((n : ℝ) + 1)) ^ 2 := by
    exact pow_lt_pow_left₀ h1 h0 two_ne_zero
  calc X.d (X.wseq n) ^ 2 - X.δ ^ 2
      ≤ (X.δ + 1 / ((n : ℝ) + 1)) ^ 2 - X.δ ^ 2 := by linarith
    _ = (2 * X.δ + 1 / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) := by ring
    _ ≤ (2 * X.δ + 1) * (1 / ((n : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = X.K₀ / ((n : ℝ) + 1) := by unfold K₀; ring

theorem norm_ι_ψ_le (n : ℕ) : ‖X.ι (X.ψ n)‖ ≤ X.δ + 1 := by
  rw [X.norm_ι_ψ]
  have h1 := X.d_wseq_lt n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

theorem δ_le_norm_ι_ψ (n : ℕ) : X.δ ≤ ‖X.ι (X.ψ n)‖ := by
  rw [X.norm_ι_ψ]; exact X.δ_le _

theorem norm_inner_sq_le_of_forall {a b : H} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ t : ℂ, δ ≤ ‖a - t • b‖) : ‖⟪b, a⟫_ℂ‖ ^ 2 ≤ (‖a‖ ^ 2 - δ ^ 2) * ‖b‖ ^ 2 := by
  by_cases hb : b = 0
  · subst hb
    simp only [inner_zero_left, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, le_refl]
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hb2 : 0 < ‖b‖ ^ 2 := by positivity
  set t : ℂ := (starRingEnd ℂ) ⟪a, b⟫_ℂ / ((‖b‖ : ℂ) ^ 2) with ht
  have hδt := h t
  have hexp : ‖a - t • b‖ ^ 2 = ‖a‖ ^ 2 - ‖⟪a, b⟫_ℂ‖ ^ 2 / ‖b‖ ^ 2 := by
    rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul]
    have hre : RCLike.re (t * ⟪a, b⟫_ℂ) = ‖⟪a, b⟫_ℂ‖ ^ 2 / ‖b‖ ^ 2 := by
      have : t * ⟪a, b⟫_ℂ = ((‖⟪a, b⟫_ℂ‖ ^ 2 / ‖b‖ ^ 2 : ℝ) : ℂ) := by
        rw [ht, div_mul_eq_mul_div, Complex.conj_mul' ⟪a, b⟫_ℂ]
        push_cast
        ring
      rw [this]; exact Complex.ofReal_re _
    have hnt : ‖t‖ = ‖⟪a, b⟫_ℂ‖ / ‖b‖ ^ 2 := by
      rw [ht, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos,
        RCLike.norm_conj]
    rw [hre, hnt]
    field_simp
    ring
  have h1 : δ ^ 2 ≤ ‖a - t • b‖ ^ 2 := pow_le_pow_left₀ hδ hδt 2
  rw [hexp] at h1
  have h2 : ‖⟪a, b⟫_ℂ‖ ^ 2 / ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 - δ ^ 2 := by linarith
  rw [div_le_iff₀ hb2] at h2
  rwa [norm_inner_symm]

theorem norm_inner_ψ_sq_le (n : ℕ) {w : L} (hw : w ∈ X.W) :
    ‖⟪X.ι w, X.ι (X.ψ n)⟫_ℂ‖ ^ 2 ≤ X.K₀ / ((n : ℝ) + 1) * ‖X.ι w‖ ^ 2 := by
  have hwS : w ∈ X.S := X.hWS hw
  have hline : ∀ t : ℂ, X.δ ≤ ‖X.ι (X.ψ n) - t • X.ι w‖ := by
    intro t
    have hmem : (X.wseq n : L) + t • w ∈ X.W := X.W.add_mem (X.wseq_mem n) (X.W.smul_mem t hw)
    have heq : X.ι (X.ψ n) - t • X.ι w = X.ι X.φ' - X.ι ((X.wseq n : L) + t • w) := by
      rw [X.ι_ψ, X.ι_add (X.wseq_memS n) (X.S.smul_mem t hwS), X.ι_smul t hwS]
      abel
    rw [heq]
    exact X.δ_le_of_mem hmem
  have h := norm_inner_sq_le_of_forall X.δ_nonneg hline
  calc ‖⟪X.ι w, X.ι (X.ψ n)⟫_ℂ‖ ^ 2 ≤ (‖X.ι (X.ψ n)‖ ^ 2 - X.δ ^ 2) * ‖X.ι w‖ ^ 2 := h
    _ ≤ X.K₀ / ((n : ℝ) + 1) * ‖X.ι w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (X.sq_norm_ι_ψ_sub_le n) (sq_nonneg _)

def r (n : ℕ) : ℝ := Real.sqrt (X.K₀ / ((n : ℝ) + 1))

theorem r_nonneg (n : ℕ) : 0 ≤ X.r n := Real.sqrt_nonneg _

theorem r_sq (n : ℕ) : X.r n ^ 2 = X.K₀ / ((n : ℝ) + 1) :=
  Real.sq_sqrt (div_nonneg X.K₀_pos.le (by positivity))

theorem norm_inner_ψ_le (n : ℕ) {w : L} (hw : w ∈ X.W) :
    ‖⟪X.ι w, X.ι (X.ψ n)⟫_ℂ‖ ≤ X.r n * ‖X.ι w‖ := by
  have h := X.norm_inner_ψ_sq_le n hw
  rw [← X.r_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (X.r_nonneg n) (norm_nonneg _))
    two_ne_zero).mp h

theorem norm_ι_ψ_sub_sq_le (n m : ℕ) :
    ‖X.ι (X.ψ n) - X.ι (X.ψ m)‖ ^ 2 ≤ 2 * (X.K₀ / ((n : ℝ) + 1)) + 2 * (X.K₀ / ((m : ℝ) + 1)) := by
  have hpar := parallelogram_law_with_norm ℂ (X.ι (X.ψ n)) (X.ι (X.ψ m))

  have hmid : (X.ι (X.ψ n) + X.ι (X.ψ m))
      = (2 : ℂ) • (X.ι X.φ' - X.ι ((2⁻¹ : ℂ) • ((X.wseq n : L) + (X.wseq m : L)))) := by
    rw [X.ι_ψ, X.ι_ψ, X.ι_smul _ (X.S.add_mem (X.wseq_memS n) (X.wseq_memS m)),
      X.ι_add (X.wseq_memS n) (X.wseq_memS m), smul_sub, smul_smul]
    norm_num
    rw [two_smul]; abel
  have hmidmem : (2⁻¹ : ℂ) • ((X.wseq n : L) + (X.wseq m : L)) ∈ X.W :=
    X.W.smul_mem _ (X.W.add_mem (X.wseq_mem n) (X.wseq_mem m))
  have hge : 2 * X.δ ≤ ‖X.ι (X.ψ n) + X.ι (X.ψ m)‖ := by
    rw [hmid, norm_smul]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (X.δ_le_of_mem hmidmem) (by norm_num)
  have hδ := X.δ_nonneg
  have hge2 : (2 * X.δ) ^ 2 ≤ ‖X.ι (X.ψ n) + X.ι (X.ψ m)‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith) hge 2
  have h1 := X.sq_norm_ι_ψ_sub_le n
  have h2 := X.sq_norm_ι_ψ_sub_le m
  nlinarith [hpar, hge2, h1, h2, sq_nonneg ‖X.ι (X.ψ n) - X.ι (X.ψ m)‖]

theorem E_ρ_ψ_mem (g : G) (n : ℕ) : X.E (X.ρ g (X.ψ n)) ∈ X.W := by
  have h : X.ρ g (X.ψ n) = X.ρ g X.φ' - X.ρ g (X.wseq n : L) := by
    unfold ψ; rw [map_sub]
  rw [h, X.E_sub (X.hS g _ X.hφ') (X.hS g _ (X.wseq_memS n))]
  exact X.W.sub_mem (X.hEφ' g) (X.hWE _ (X.hWρ g _ (X.wseq_mem n)))

theorem norm_ι_E_ρ_ψ_le (g : G) (n : ℕ) :
    ‖X.ι (X.E (X.ρ g (X.ψ n)))‖ ≤ X.c g * Real.sqrt (X.c g⁻¹) * X.r n := by
  set u := X.E (X.ρ g (X.ψ n)) with hu
  have huW : u ∈ X.W := X.E_ρ_ψ_mem g n
  have huS : u ∈ X.S := X.hWS huW
  have hρψS : X.ρ g (X.ψ n) ∈ X.S := X.hS g _ (X.ψ_memS n)
  have hPu : X.P u := X.hEP _ hρψS

  have h1 : ⟪X.ι u, X.ι u⟫_ℂ = ⟪X.ι (X.ρ g (X.ψ n)), X.ι u⟫_ℂ := X.hEinner _ hρψS u huS hPu
  have h2 : ⟪X.ι (X.ρ g (X.ψ n)), X.ι u⟫_ℂ
      = (X.c g : ℂ) * ⟪X.ι (X.ψ n), X.ι (X.ρ g⁻¹ u)⟫_ℂ := by
    conv_lhs => rw [← X.ρ_inv_apply g u]
    exact X.inner_ι_ρ g (X.ψ_memS n) (X.hS g⁻¹ u huS)
  have hmemW : X.ρ g⁻¹ u ∈ X.W := X.hWρ g⁻¹ u huW
  have h3 : ‖⟪X.ι (X.ψ n), X.ι (X.ρ g⁻¹ u)⟫_ℂ‖ ≤ X.r n * ‖X.ι (X.ρ g⁻¹ u)‖ := by
    rw [← norm_inner_symm]; exact X.norm_inner_ψ_le n hmemW
  have h4 : ‖X.ι (X.ρ g⁻¹ u)‖ = Real.sqrt (X.c g⁻¹) * ‖X.ι u‖ := X.norm_ι_ρ g⁻¹ huS
  have hsq : ‖X.ι u‖ ^ 2 ≤ X.c g * (X.r n * (Real.sqrt (X.c g⁻¹) * ‖X.ι u‖)) := by
    have : ‖X.ι u‖ ^ 2 = ‖⟪X.ι u, X.ι u⟫_ℂ‖ := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast; simp [abs_of_nonneg]
    rw [this, h1, h2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (X.hc g)]
    apply mul_le_mul_of_nonneg_left _ (X.hc g).le
    rw [← h4]; exact h3
  have hcpos := X.hc g
  have hrn := X.r_nonneg n
  have hsc : 0 ≤ Real.sqrt (X.c g⁻¹) := Real.sqrt_nonneg _
  by_cases h0 : ‖X.ι u‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖X.ι u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖X.ι u‖ * ‖X.ι u‖ ≤ (X.c g * Real.sqrt (X.c g⁻¹) * X.r n) * ‖X.ι u‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

def Small (v : L) : Prop := ∃ C : ℝ, ∀ n : ℕ, ‖⟪X.ι v, X.ι (X.ψ n)⟫_ℂ‖ ≤ C * X.r n

theorem small_ρ_φ (x : G) : X.Small (X.ρ x X.φ) := by
  refine ⟨X.c x * ‖X.ι X.φ‖ * (X.c x⁻¹ * Real.sqrt (X.c x⁻¹⁻¹)), fun n => ?_⟩
  have hψS := X.ψ_memS n

  have h1 : ⟪X.ι (X.ρ x X.φ), X.ι (X.ψ n)⟫_ℂ
      = (X.c x : ℂ) * ⟪X.ι X.φ, X.ι (X.ρ x⁻¹ (X.ψ n))⟫_ℂ := by
    conv_lhs => rw [← X.ρ_inv_apply x (X.ψ n)]
    exact X.inner_ι_ρ x X.hφ (X.hS x⁻¹ _ hψS)

  have hmemS : X.ρ x⁻¹ (X.ψ n) ∈ X.S := X.hS x⁻¹ _ hψS
  have h2 : ⟪X.ι X.φ, X.ι (X.ρ x⁻¹ (X.ψ n))⟫_ℂ
      = (starRingEnd ℂ) ⟪X.ι (X.E (X.ρ x⁻¹ (X.ψ n))), X.ι X.φ⟫_ℂ := by
    rw [X.hEinner _ hmemS X.φ X.hφ X.hPφ, inner_conj_symm]
  have h3 := X.norm_ι_E_ρ_ψ_le x⁻¹ n
  rw [h1, h2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (X.hc x),
    RCLike.norm_conj]
  calc X.c x * ‖⟪X.ι (X.E (X.ρ x⁻¹ (X.ψ n))), X.ι X.φ⟫_ℂ‖
      ≤ X.c x * (‖X.ι (X.E (X.ρ x⁻¹ (X.ψ n)))‖ * ‖X.ι X.φ‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (X.hc x).le
    _ ≤ X.c x * (X.c x⁻¹ * Real.sqrt (X.c x⁻¹⁻¹) * X.r n * ‖X.ι X.φ‖) := by
        apply mul_le_mul_of_nonneg_left _ (X.hc x).le
        exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = X.c x * ‖X.ι X.φ‖ * (X.c x⁻¹ * Real.sqrt (X.c x⁻¹⁻¹)) * X.r n := by ring

theorem small_zero : X.Small 0 := ⟨0, fun n => by simp [X.ι_zero]⟩

theorem small_add {v₁ v₂ : L} (h₁S : v₁ ∈ X.S) (h₂S : v₂ ∈ X.S) (h₁ : X.Small v₁)
    (h₂ : X.Small v₂) : X.Small (v₁ + v₂) := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun n => ?_⟩
  rw [X.ι_add h₁S h₂S, inner_add_left]
  calc ‖⟪X.ι v₁, X.ι (X.ψ n)⟫_ℂ + ⟪X.ι v₂, X.ι (X.ψ n)⟫_ℂ‖
      ≤ ‖⟪X.ι v₁, X.ι (X.ψ n)⟫_ℂ‖ + ‖⟪X.ι v₂, X.ι (X.ψ n)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ C₁ * X.r n + C₂ * X.r n := add_le_add (hC₁ n) (hC₂ n)
    _ = (C₁ + C₂) * X.r n := by ring

theorem small_smul (a : ℂ) {v : L} (hvS : v ∈ X.S) (h : X.Small v) : X.Small (a • v) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖a‖ * C, fun n => ?_⟩
  rw [X.ι_smul a hvS, inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)

theorem small_of_mem_V {v : L} (hv : v ∈ X.V X.φ) : X.Small v := by
  induction hv using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, rfl⟩ := hu
    exact X.small_ρ_φ x
  | zero => exact X.small_zero
  | add u u' hu hu' ihu ihu' =>
    exact X.small_add (X.V_le_S X.hφ hu) (X.V_le_S X.hφ hu') ihu ihu'
  | smul a u hu ihu => exact X.small_smul a (X.V_le_S X.hφ hu) ihu

theorem exists_r_le (η : ℝ) (hη : 0 < η) : ∃ N : ℕ, ∀ n, N ≤ n → X.r n ≤ η := by
  obtain ⟨N, hN⟩ := exists_nat_gt (X.K₀ / η ^ 2)
  refine ⟨N, fun n hn => ?_⟩
  have hK := X.K₀_pos
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hle : X.K₀ / ((n : ℝ) + 1) ≤ η ^ 2 := by
    rw [div_le_iff₀ hn1]
    have : X.K₀ / η ^ 2 < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ (by positivity)] at this
    linarith
  unfold r
  calc Real.sqrt (X.K₀ / ((n : ℝ) + 1)) ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt hle
    _ = η := Real.sqrt_sq hη.le

theorem δ_sq_le (η : ℝ) (hη : 0 < η) : X.δ ^ 2 ≤ (2 * (X.δ + 1) + 1) * η := by

  obtain ⟨N₁, hN₁⟩ := X.exists_r_le (η / 2) (by positivity)

  have happrox : X.Approx (X.ψ N₁) :=
    X.approx_sub X.hφ' (X.wseq_memS N₁) X.approx_φ' (X.approx_of_mem_W (X.wseq_mem N₁))
  obtain ⟨v, hv, hvlt⟩ := happrox η hη
  have hvS : v ∈ X.S := X.V_le_S X.hφ hv
  obtain ⟨C, hC⟩ := X.small_of_mem_V hv

  obtain ⟨N₂, hN₂⟩ := X.exists_r_le (η / (|C| + 1)) (by positivity)
  set n := max N₁ N₂ with hn
  have hn₁ : N₁ ≤ n := le_max_left _ _
  have hn₂ : N₂ ≤ n := le_max_right _ _

  set a := X.ι (X.ψ n) with ha
  have hK₁ : ‖a‖ ≤ X.δ + 1 := X.norm_ι_ψ_le n
  have hδa : X.δ ≤ ‖a‖ := X.δ_le_norm_ι_ψ n
  have hδ := X.δ_nonneg

  have hcauchy : ‖a - X.ι (X.ψ N₁)‖ ≤ η := by
    have h := X.norm_ι_ψ_sub_sq_le n N₁
    have hr1 : X.r n ≤ η / 2 := hN₁ n hn₁
    have hr2 : X.r N₁ ≤ η / 2 := hN₁ N₁ le_rfl
    have e1 : X.K₀ / ((n : ℝ) + 1) = X.r n ^ 2 := (X.r_sq n).symm
    have e2 : X.K₀ / ((N₁ : ℝ) + 1) = X.r N₁ ^ 2 := (X.r_sq N₁).symm
    rw [e1, e2] at h
    have hb : ‖a - X.ι (X.ψ N₁)‖ ^ 2 ≤ η ^ 2 := by
      have := X.r_nonneg n
      have := X.r_nonneg N₁
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hη.le two_ne_zero).mp hb

  have hdecomp : ⟪a, a⟫_ℂ = ⟪a, a - X.ι (X.ψ N₁)⟫_ℂ + ⟪a, X.ι (X.ψ N₁) - X.ι v⟫_ℂ
      + (starRingEnd ℂ) ⟪X.ι v, a⟫_ℂ := by
    rw [inner_conj_symm, ← inner_add_right, ← inner_add_right]
    congr 1; abel
  have hnorm : ‖a‖ ^ 2 = ‖⟪a, a⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast; simp [abs_of_nonneg]
  have hpair : ‖⟪X.ι v, a⟫_ℂ‖ ≤ η := by
    calc ‖⟪X.ι v, a⟫_ℂ‖ ≤ C * X.r n := hC n
      _ ≤ |C| * X.r n := mul_le_mul_of_nonneg_right (le_abs_self C) (X.r_nonneg n)
      _ ≤ (|C| + 1) * X.r n := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C]) (X.r_nonneg n)
      _ ≤ (|C| + 1) * (η / (|C| + 1)) :=
          mul_le_mul_of_nonneg_left (hN₂ n hn₂) (by positivity)
      _ = η := mul_div_cancel₀ η (by positivity)
  have hbound : ‖a‖ ^ 2 ≤ ‖a‖ * η + ‖a‖ * η + η := by
    rw [hnorm, hdecomp]
    calc ‖⟪a, a - X.ι (X.ψ N₁)⟫_ℂ + ⟪a, X.ι (X.ψ N₁) - X.ι v⟫_ℂ + (starRingEnd ℂ) ⟪X.ι v, a⟫_ℂ‖
        ≤ ‖⟪a, a - X.ι (X.ψ N₁)⟫_ℂ‖ + ‖⟪a, X.ι (X.ψ N₁) - X.ι v⟫_ℂ‖
            + ‖(starRingEnd ℂ) ⟪X.ι v, a⟫_ℂ‖ := norm_add₃_le
      _ ≤ ‖a‖ * ‖a - X.ι (X.ψ N₁)‖ + ‖a‖ * ‖X.ι (X.ψ N₁) - X.ι v‖ + ‖⟪X.ι v, a⟫_ℂ‖ := by
          rw [RCLike.norm_conj]
          exact add_le_add (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)) le_rfl
      _ ≤ ‖a‖ * η + ‖a‖ * η + η :=
          add_le_add_three (mul_le_mul_of_nonneg_left hcauchy (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hvlt.le (norm_nonneg _)) hpair
  calc X.δ ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ hδ hδa 2
    _ ≤ ‖a‖ * η + ‖a‖ * η + η := hbound
    _ ≤ (X.δ + 1) * η + (X.δ + 1) * η + η := by gcongr
    _ = (2 * (X.δ + 1) + 1) * η := by ring

theorem δ_eq_zero : X.δ = 0 := by
  have hδ := X.δ_nonneg
  by_contra hne
  have hpos : 0 < X.δ := lt_of_le_of_ne hδ (Ne.symm hne)
  have hA : 0 < 2 * (X.δ + 1) + 1 := by linarith
  set η := X.δ ^ 2 / (2 * (2 * (X.δ + 1) + 1)) with hη
  have hηpos : 0 < η := by positivity
  have h := X.δ_sq_le η hηpos
  have : (2 * (X.δ + 1) + 1) * η = X.δ ^ 2 / 2 := by
    rw [hη]; field_simp
  rw [this] at h
  have : 0 < X.δ ^ 2 := by positivity
  linarith

theorem main (ε : ℝ) (hε : 0 < ε) : ∃ w ∈ X.W, ‖X.ι X.φ' - X.ι w‖ < ε := by
  obtain ⟨w, hw⟩ := X.exists_d_lt ε hε
  rw [X.δ_eq_zero, zero_add] at hw
  exact ⟨w, w.2, hw⟩

end Setup
p2m_reactivate "P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.CyclicLevelAverageEngine.Setup"

end CyclicLevelAverageEngine
p2m_reactivate "P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.CyclicLevelAverageEngine.Setup P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.CyclicLevelAverageEngine"

end
p2m_reactivate "P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.CyclicLevelAverageEngine.Setup P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.CyclicLevelAverageEngine"

open CyclicLevelAverageEngine in
theorem solution
    {G : Type*} [Group G] {L : Type*} [AddCommGroup L] [Module ℂ L]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (L →ₗ[ℂ] L)) (S : Submodule ℂ L) (hS : ∀ x : G, ∀ f ∈ S, ρ x f ∈ S)
    (ι : L → H)
    (hι : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → ι (a • f + b • g) = a • ι f + b • ι g)
    (c : G → ℝ) (hc : ∀ x, 0 < c x)
    (hρ : ∀ x : G, ∀ f ∈ S, ‖ι (ρ x f)‖ ^ 2 = c x * ‖ι f‖ ^ 2)
    (P : L → Prop) (E : L → L)
    (hE : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → E (a • f + b • g) = a • E f + b • E g)
    (hEP : ∀ f ∈ S, P (E f))
    (hEinner : ∀ f ∈ S, ∀ g ∈ S, P g → ⟪ι (E f), ι g⟫_ℂ = ⟪ι f, ι g⟫_ℂ)
    (φ φ' : L) (hφ : φ ∈ S) (hPφ : P φ) (hφ' : φ' ∈ S)
    (hspan : ∀ ε : ℝ, 0 < ε →
      ∃ v ∈ Submodule.span ℂ (Set.range fun x : G => ρ x φ), ‖ι φ' - ι v‖ < ε)
    (W : Submodule ℂ L) (hWS : W ≤ S)
    (hWφ' : W ≤ Submodule.span ℂ (Set.range fun x : G => ρ x φ'))
    (hWρ : ∀ x : G, ∀ w ∈ W, ρ x w ∈ W) (hWE : ∀ w ∈ W, E w ∈ W)
    (hEφ' : ∀ x : G, E (ρ x φ') ∈ W) :
    ∀ ε : ℝ, 0 < ε → ∃ w ∈ W, ‖ι φ' - ι w‖ < ε := by
  intro ε hε
  let X : Setup G L H :=
    { ρ := ρ, S := S, hS := hS, ι := ι, hι := hι, c := c, hc := hc, hρ := hρ, P := P, E := E,
      hE := hE, hEP := hEP, hEinner := hEinner, φ := φ, φ' := φ', hφ := hφ, hPφ := hPφ,
      hφ' := hφ', hspan := hspan, W := W, hWS := hWS, hWφ' := hWφ', hWρ := hWρ, hWE := hWE,
      hEφ' := hEφ' }
  exact X.main ε hε

end S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
end P2MW
export P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average (solution)
