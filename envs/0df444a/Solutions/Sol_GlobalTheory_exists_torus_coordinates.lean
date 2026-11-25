-- Prove2me | solution 1 for GlobalTheory.exists_torus_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:26.8548+00:00
-- url     : https://prove2.me/submissions/597de80f-aae9-4774-8aaa-cca1ac3f6f07

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_GlobalTheory_TorusCoord_sum_emb_split
import Theorems.Thm_GlobalTheory_TorusCoord_c_pos
import Theorems.Thm_GlobalTheory_TorusCoord_finrank_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_conj_conj_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_sum_castLE_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_sum_shift_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
namespace GlobalTheory
namespace TorusCoord
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end TorusCoord
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem coord_eq_pr_of_mem_psi (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X τ.1)) :
    _root_.GlobalTheory.TorusCoord.coord X e y ⟨τ.1, a⟩ =
      _root_.GlobalTheory.TorusCoord.pr X e y τ ⟨a.1, _root_.GlobalTheory.TorusCoord.lt_pos X τ.2 a⟩ := by
  unfold _root_.GlobalTheory.TorusCoord.coord
  rw [dif_pos τ.2]
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem coord_conjugate_eq_neg_conj_pr (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1))) :
    _root_.GlobalTheory.TorusCoord.coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ =
      -conj (_root_.GlobalTheory.TorusCoord.pr X e y τ
        ⟨X.p0 + a.1, _root_.GlobalTheory.TorusCoord.lt_neg X ((X.cmType τ.1).mp τ.2) a⟩) := by
  have h : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := (X.cmType τ.1).mp τ.2
  have hτ : (⟨ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1),
      _root_.GlobalTheory.TorusCoord.conj_mem X h⟩ : X.Ψ) = τ := Subtype.ext (_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X _)
  unfold _root_.GlobalTheory.TorusCoord.coord
  rw [dif_neg h, hτ]
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem sum_idx_eq_sum_sigma {dim : (E →+* ℂ) → ℕ} (G : _root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim → ℝ) :
    ∑ i, G i = ∑ σ, ∑ a : Fin (dim σ), G ⟨σ, a⟩ := Fintype.sum_sigma G
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem torusCoordinates_pair_im_lemma_4 (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (he : ∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0)
    (y y' : X.Ψ → Fin r → ℂ) (τ : X.Ψ) :
    ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X τ.1),
        (_root_.GlobalTheory.TorusCoord.coord X e y ⟨τ.1, a⟩ *
          conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨τ.1, a⟩)).im +
      ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1)),
        (_root_.GlobalTheory.TorusCoord.coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ *
          conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨ComplexEmbedding.conjugate τ.1, a⟩)).im =
      X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (y' τ)).im := by
  set g : Fin r → ℝ := fun b => (_root_.GlobalTheory.TorusCoord.pr X e y τ b *
    conj (_root_.GlobalTheory.TorusCoord.pr X e y' τ b)).im with hg
  have hnot : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := (X.cmType τ.1).mp τ.2
  have hpos : _root_.GlobalTheory.TorusCoord.dimOf X τ.1 = X.p0 := if_pos τ.2
  have hneg : _root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1) = r - X.p0 := if_neg hnot
  have hle : _root_.GlobalTheory.TorusCoord.dimOf X τ.1 ≤ r := hpos ▸ X.p0_le
  have e1 : ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X τ.1),
      (_root_.GlobalTheory.TorusCoord.coord X e y ⟨τ.1, a⟩ *
        conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨τ.1, a⟩)).im = ∑ b : Fin r with b.val < X.p0, g b := by
    simp only [coord_eq_pr_of_mem_psi]
    refine (_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.sum_castLE_eq hle g).trans ?_
    rw [hpos]
  have e2 : ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1)),
      (_root_.GlobalTheory.TorusCoord.coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ *
        conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨ComplexEmbedding.conjugate τ.1, a⟩)).im =
      -∑ b : Fin r with ¬ b.val < X.p0, g b := by
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.sum_shift_eq X.p0_le hneg g
      (fun a => (⟨X.p0 + a.1, _root_.GlobalTheory.TorusCoord.lt_neg X hnot a⟩ : Fin r)) (fun _ => rfl),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coord_conjugate_eq_neg_conj_pr, coord_conjugate_eq_neg_conj_pr, hg]
    simp only [map_neg, Complex.conj_conj, neg_mul_neg, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hs : (Real.sqrt (X.c τ) : ℂ) * (Real.sqrt (X.c τ) : ℂ) = (X.c τ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (_root_.GlobalTheory.TorusCoord.c_pos X τ).le]
  have hterm : ∀ b : Fin r, X.c τ * ((starRingEnd ℂ) (((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 b : ℝ) : ℂ) *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b)) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b)).im = _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 b * g b := by
    intro b
    have hgb : g b = X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) *
        conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b))).im := by
      rw [hg]
      simp only [_root_.GlobalTheory.TorusCoord.pr, map_mul, Complex.conj_ofReal]
      rw [show (Real.sqrt (X.c τ) : ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) *
          ((Real.sqrt (X.c τ) : ℂ) * conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b))) =
          ((Real.sqrt (X.c τ) : ℂ) * (Real.sqrt (X.c τ) : ℂ)) *
            (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) * conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b))) by ring,
        hs, Complex.im_ofReal_mul]
    rw [hgb, map_mul, Complex.conj_ofReal, mul_assoc, Complex.im_ofReal_mul,
      mul_comm (conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b)))]
    ring
  rw [e1, e2, _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.expand X τ (e τ) (he τ) (y' τ), _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right]
  rw [Complex.im_sum, Finset.mul_sum]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun b _ => (hterm b).symm)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin r => (b : ℕ) < X.p0),
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter] at hb
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, hb.2]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter] at hb
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, hb.2]
end GlobalTheory
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
open GlobalTheory
open NumberField
open scoped ComplexConjugate
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) → ∃ (dim : (E →+* ℂ) → ℕ) (hp : ∀ τ : X.Ψ, dim τ.1 = X.p0) (hn : ∀ τ : X.Ψ, dim (ComplexEmbedding.conjugate τ.1) = r - X.p0) (Φ : (X.Ψ → Fin r → ℂ) ≃ₗ[ℝ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim), Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim) = X.Ψ.card * r ∧ (∀ τ, dim τ + dim (ComplexEmbedding.conjugate τ) = r) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim τ.1)), (Φ y) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ (Fin.castLE (by rw [hp τ]; exact X.p0_le) a))) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim (ComplexEmbedding.conjugate τ.1))), (Φ y) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * (starRingEnd ℂ) (-_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (hn τ); have := X.p0_le; omega⟩))) ∧ (∀ (α : 𝓞 E) y, Φ (fun τ => τ.1 (α : E) • y τ) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (Φ y)) ∧ ∀ y y', (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (Φ y) (Φ y')).im = ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (y' τ)).im := by
  intro E _ _ _ r X e he
  have hp : ∀ τ : X.Ψ, _root_.GlobalTheory.TorusCoord.dimOf X τ.1 = X.p0 := fun τ => if_pos τ.2
  have hn : ∀ τ : X.Ψ, _root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1) = r - X.p0 :=
    fun τ => if_neg ((X.cmType τ.1).mp τ.2)
  have hsum : ∀ σ, _root_.GlobalTheory.TorusCoord.dimOf X σ +
      _root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate σ) = r := by
    intro σ
    have := X.p0_le
    by_cases hσ : σ ∈ X.Ψ
    · rw [_root_.GlobalTheory.TorusCoord.dimOf, _root_.GlobalTheory.TorusCoord.dimOf, if_pos hσ, if_neg ((X.cmType σ).mp hσ)]
      omega
    · rw [_root_.GlobalTheory.TorusCoord.dimOf, _root_.GlobalTheory.TorusCoord.dimOf, if_neg hσ,
        if_pos (_root_.GlobalTheory.TorusCoord.conj_mem X hσ)]
      omega
  have hcard : Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx (_root_.GlobalTheory.TorusCoord.dimOf X)) = X.Ψ.card * r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [_root_.GlobalTheory.TorusCoord.sum_emb_split X]
    simp [hsum]
  have hdim : Module.finrank ℝ (X.Ψ → Fin r → ℂ) =
      Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp (_root_.GlobalTheory.TorusCoord.dimOf X)) := by
    have h1 : Module.finrank ℝ (X.Ψ → Fin r → ℂ) = X.Ψ.card * r * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
      ring
    have h2 : Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp (_root_.GlobalTheory.TorusCoord.dimOf X)) =
        Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx (_root_.GlobalTheory.TorusCoord.dimOf X)) * 2 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp
      rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    rw [h1, h2, hcard]
  have hc : ∀ τ : X.Ψ, (Real.sqrt (X.c τ) : ℂ) ≠ 0 := fun τ => by
    exact_mod_cast (Real.sqrt_pos.mpr (_root_.GlobalTheory.TorusCoord.c_pos X τ)).ne'
  have hinj : Function.Injective (_root_.GlobalTheory.TorusCoord.coordMap X e) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, _root_.GlobalTheory.TorusCoord.coord X e y i = 0 := fun i =>
      congrArg (fun v : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp (_root_.GlobalTheory.TorusCoord.dimOf X) => v i) hy
    funext τ
    have hz : ∀ b : Fin r, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) = 0 := by
      intro b
      have key : _root_.GlobalTheory.TorusCoord.pr X e y τ b = 0 := by
        have hb' := b.2
        by_cases hb : (b : ℕ) < X.p0
        · have h1 := hy' ⟨τ.1, ⟨b.1, by rw [hp τ]; exact hb⟩⟩
          rw [coord_eq_pr_of_mem_psi] at h1
          exact h1
        · have h2 := hy' ⟨ComplexEmbedding.conjugate τ.1, ⟨b.1 - X.p0, by rw [hn τ]; omega⟩⟩
          rw [coord_conjugate_eq_neg_conj_pr, neg_eq_zero, map_eq_zero] at h2
          convert h2 using 3
          first
            | (simp only [Fin.val_mk]; omega)
            | (ext; simp only [Fin.val_mk]; omega)
      exact (mul_eq_zero.mp key).resolve_left (hc τ)
    show y τ = 0
    rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.expand X τ (e τ) (he τ) (y τ)]
    simp [hz]
  refine ⟨_root_.GlobalTheory.TorusCoord.dimOf X, hp, hn,
    LinearMap.linearEquivOfInjective (_root_.GlobalTheory.TorusCoord.coordMap X e) hinj hdim, hcard, hsum,
    ?_, ?_, ?_, ?_⟩
  · intro y τ a
    exact coord_eq_pr_of_mem_psi X e y τ a
  · intro y τ a
    refine (coord_conjugate_eq_neg_conj_pr X e y τ a).trans ?_
    simp only [_root_.GlobalTheory.TorusCoord.pr, map_mul, map_neg, Complex.conj_ofReal]
    ring
  · intro α y
    refine PiLp.ext fun i => ?_
    change _root_.GlobalTheory.TorusCoord.coord X e (fun τ => τ.1 (α : E) • y τ) i =
      i.1 (α : E) * _root_.GlobalTheory.TorusCoord.coord X e y i
    unfold _root_.GlobalTheory.TorusCoord.coord
    split_ifs with hσ
    · simp only [_root_.GlobalTheory.TorusCoord.pr, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left]
      ring
    · simp only [_root_.GlobalTheory.TorusCoord.pr, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, map_mul, map_neg,
        ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, Complex.conj_ofReal]
      ring
  · intro y y'
    change (∑ i : _root_.ReciprocityTheory.ChartRestriction.G.I2.Idx (_root_.GlobalTheory.TorusCoord.dimOf X), _root_.GlobalTheory.TorusCoord.coord X e y i *
      conj (_root_.GlobalTheory.TorusCoord.coord X e y' i)).im = _
    rw [Complex.im_sum, sum_idx_eq_sum_sigma, _root_.GlobalTheory.TorusCoord.sum_emb_split X]
    exact Finset.sum_congr rfl fun τ _ => torusCoordinates_pair_im_lemma_4 X e he y y' τ
end _root_.GlobalTheory
end GlobalTheory
