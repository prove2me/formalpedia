-- Prove2me | solution 1 for GlobalTheory.per_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:37:41.527035+00:00
-- url     : https://prove2.me/submissions/71b5c095-f8ca-4a1e-82c2-3120a01ca342

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Theorems.Thm_GlobalTheory_PerMove_differentiable_det
import Theorems.Thm_GlobalTheory_PerMove_inv_mulVec_apply
import Theorems.Thm_GlobalTheory_PerMove_det_of_triangular
import Theorems.Thm_GlobalTheory_PerMove_hermC_unitary
import Theorems.Thm_GlobalTheory_PerMove_emb_mulVec
import Theorems.Thm_GlobalTheory_PerMove_col_mul
import Theorems.Thm_GlobalTheory_PerMove_hermC_col_mul
import Theorems.Thm_GlobalTheory_PerMove_bor_tri
import Theorems.Thm_GlobalTheory_PerMove_bor_inv_tri
import Theorems.Thm_GlobalTheory_PerMove_bor_inv_diag
import Theorems.Thm_GlobalTheory_PerMove_rmul_mem_GG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PerMove
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end GlobalTheory.PerMove
namespace GlobalTheory
open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma differentiable_hermC_col_mat {Ψ : Finset (E →+* ℂ)} (G : Matrix (Fin r) (Fin r) E)
    (σ : Ψ) (a : Fin r) (w : Fin r → ℂ) :
    Differentiable ℂ fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC σ.1 G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x σ) a) w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC _root_.ReciprocityTheory.ChartRestriction.G.FD.col _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  simp only [Matrix.of_apply]
  fun_prop
open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma differentiableOn_mat_inv_mulVec_apply {Ψ : Finset (E →+* ℂ)} (s : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r))
    (hs : ∀ x ∈ s, ∀ σ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x σ).det ≠ 0) (σ : Ψ) (a : Fin r) (w : Fin r → ℂ) :
    DifferentiableOn ℂ (fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x σ)⁻¹ *ᵥ w) a) s := by
  simp only [_root_.GlobalTheory.PerMove.inv_mulVec_apply]
  refine DifferentiableOn.mul ?_ ?_
  · refine DifferentiableOn.inv ?_ fun x hx => hs x hx σ
    refine (_root_.GlobalTheory.PerMove.differentiable_det _ fun i j => ?_).differentiableOn
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat; simp only [Matrix.of_apply]; fun_prop
  · refine (_root_.GlobalTheory.PerMove.differentiable_det _ fun i j => ?_).differentiableOn
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    split_ifs <;> fun_prop
open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
private lemma sum_ite_fst_eq_sum_symm {Ψ : Finset (E →+* ℂ)} [DecidableEq Ψ] {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (σ : Ψ)
    (F : Fin g → ℂ) (c : Fin r → ℂ) :
    ∑ l, (if (idx l).1 = σ then c (idx l).2 else 0) * F l = ∑ a, c a * F (idx.symm (σ, a)) := by
  rw [← idx.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, ite_mul, zero_mul, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    simp [hτ]
  · intro h; exact absurd (Finset.mem_univ σ) h
end GlobalTheory
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
        : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D
        : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm
        : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ
        : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+*
        ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx
        k).1.1 else (idx
        k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ
        ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
        (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
        ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ *
        _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ
        y))) → (∀ P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r → (D.La →+ (Fin g →
        ℂ)), (∀ x, (∀ v k, P x v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2)) → ∀ v, DifferentiableOn ℂ (fun x => P x v) (_root_.ReciprocityTheory.ChartRestriction.G.FD.GG
        Ψ Gm D.q)) ∧ (∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (γ : GL (Fin
        r) E) (P P' : D.La →+ (Fin g →
        ℂ)), (∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm ((γ : Matrix (Fin
        r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ
        v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm u v) → (∀ v k, P v k = if ((idx
        k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → (∀ v k, P' v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → ∀ v v', φ v' = (γ : Matrix (Fin r) (Fin
        r) E) *ᵥ φ v → P' v' = P v) ∧ ∀ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ Gm D.q, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r, ∀ (P
        P' : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → (∀ v k, P' v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ Gm D.q ∧ ∃ h : Matrix (Fin
        g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) ∧ (∀ k, h k k = if ((idx k).2 : ℕ) < D.q then b (idx
        k).1 (idx k).2 (idx k).2 else (b (idx k).1 (idx k).2 (idx
        k).2)⁻¹) ∧ h.det = ∏ k, h k k := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro P hP v
    rw [differentiableOn_pi]
    intro k
    simp only [hP]
    split_ifs
    · exact (differentiable_hermC_col_mat Gm _ _ _).differentiableOn
    · exact differentiableOn_mat_inv_mulVec_apply _ (fun x hx σ => (hx σ).1) _ _ _
  · intro x γ P P' hγ hP hP' v v' hv
    funext k
    rw [hP', hP, hv]
    have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1 =
        (γ : Matrix (Fin r) (Fin r) E).map (idx k).1.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1 := rfl
    rw [hmat, _root_.GlobalTheory.PerMove.emb_mulVec]
    split_ifs
    · rw [_root_.GlobalTheory.PerMove.col_mul, _root_.GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
    · have hunit : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map (idx k).1.1).det := by
        rw [show ((γ : Matrix (Fin r) (Fin r) E).map (idx k).1.1).det =
            (idx k).1.1 (γ : Matrix (Fin r) (Fin r) E).det from (RingHom.map_det _ _).symm]
        exact ((Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit).map _
      rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
        Matrix.mul_one]
  · intro x hx b hb P P' hP hP'
    refine ⟨_root_.GlobalTheory.PerMove.rmul_mem_GG hx hb, ?_⟩
    classical
    let coeff : Fin g → Fin r → ℂ := fun k c =>
      if ((idx k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1 c (idx k).2
      else (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1)⁻¹ (idx k).2 c
    let h : Matrix (Fin g) (Fin g) ℂ :=
      Matrix.of fun k l => if (idx l).1 = (idx k).1 then coeff k (idx l).2 else 0
    refine ⟨h, fun v => ?_, fun k => ?_, ?_⟩
    · funext k
      have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1 = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1 := rfl
      rw [hP', hmat, show (h *ᵥ P v) k = ∑ l, h k l * P v l from rfl]
      simp only [h, Matrix.of_apply]
      rw [sum_ite_fst_eq_sum_symm]
      simp only [hP, Equiv.apply_symm_apply, coeff]
      split_ifs with hk
      · rw [_root_.GlobalTheory.PerMove.hermC_col_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs with hc
        · rfl
        · rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1 c (idx k).2 = 0 from _root_.GlobalTheory.PerMove.bor_tri hb _ (by
            simp only [id_eq, Fin.lt_def]; omega), zero_mul, zero_mul]
      · rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs with hc
        · rw [show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1)⁻¹ (idx k).2 c = 0 from _root_.GlobalTheory.PerMove.bor_inv_tri hb _ (by
            simp only [id_eq, Fin.lt_def]; omega), zero_mul, zero_mul]
        · rfl
    · simp only [h, coeff, Matrix.of_apply, if_true]
      split_ifs
      · rfl
      · exact _root_.GlobalTheory.PerMove.bor_inv_diag hb _ _
    · let key : Fin r → ℤ := fun a => if (a : ℕ) < D.q then -(a : ℤ) else a
      let f : Fin g → ℕ ×ₗ ℤ := fun k => toLex ((Fintype.equivFin Ψ (idx k).1 : ℕ), key (idx k).2)
      have hkey : ∀ a c : Fin r, key a = key c → a = c := by
        intro a c hac
        simp only [key] at hac
        ext
        split_ifs at hac <;> omega
      refine _root_.GlobalTheory.PerMove.det_of_triangular f (fun k l hkl => ?_) h fun k l hlt => ?_
      · simp only [f, toLex_inj, Prod.mk.injEq] at hkl
        apply idx.injective
        exact Prod.ext ((Fintype.equivFin Ψ).injective (Fin.ext hkl.1)) (hkey _ _ hkl.2)
      · simp only [h, Matrix.of_apply]
        split_ifs with hσ
        · have hk : key (idx l).2 < key (idx k).2 := by
            rcases (Prod.Lex.toLex_lt_toLex).mp hlt with h1 | ⟨_, h2⟩
            · simp only [hσ] at h1
              exact absurd h1 (lt_irrefl _)
            · exact h2
          simp only [key] at hk
          simp only [coeff]
          split_ifs with ha
          · exact _root_.GlobalTheory.PerMove.bor_tri hb _ (by simp only [id_eq, Fin.lt_def]; split_ifs at hk <;> omega)
          · exact _root_.GlobalTheory.PerMove.bor_inv_tri hb _ (by simp only [id_eq, Fin.lt_def]; split_ifs at hk <;> omega)
        · rfl
end _root_.GlobalTheory
end GlobalTheory
