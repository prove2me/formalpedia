-- Prove2me | solution 1 for GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:37:15.426407+00:00
-- url     : https://prove2.me/submissions/3084731a-7729-4980-8e3d-ab0f2d6c8716

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIcoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegular
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_conj
import Theorems.Thm_GlobalTheory_BI_irr_of_norm_one
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_ipGL_psi_eq
import Theorems.Thm_GlobalTheory_CuspGL_extZero_spec
import Theorems.Thm_GlobalTheory_CuspGL_ipGL_psi_rootSum
import Theorems.Thm_GlobalTheory_CuspGL_isPrimitive_psi
import Theorems.Thm_GlobalTheory_CuspGL_psi_conj
import Theorems.Thm_GlobalTheory_CuspGL_psi_eq
import Theorems.Thm_GlobalTheory_CuspGL_psi_one
import Theorems.Thm_GlobalTheory_CuspGL_rootSum_charpoly_mem_virt
import Theorems.Thm_GlobalTheory_CuspGL_rootSum_isAdditive_and_pow_X_sub_one
import Theorems.Thm_GlobalTheory_IsLogBounded_conj
import Theorems.Thm_GlobalTheory_ParabVirt_parab_virt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL
open Polynomial in
private lemma finsum_proper_invariant_eq_sum_range_finrank {F : Type} [Field F] [Finite F] (d : ℕ)
    (g : Module.End F (Fin d → F)) (Ψ : ∀ W : Submodule F (Fin d → F), (∀ v ∈ W, g v ∈ W) → ℂ) :
    (∑ᶠ (W : { W : Submodule F (Fin d → F) // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W }), Ψ W.1 W.2.2) =
    ∑ a ∈ Finset.range d, ∑ᶠ (W : { W : Submodule F (Fin d → F) //
      Module.finrank F W = a ∧ ∀ v ∈ W, g v ∈ W }), Ψ W.1 W.2.2 := by
  classical
  have : Fintype (Submodule F (Fin d → F)) := Fintype.ofFinite _
  let Fn : Submodule F (Fin d → F) → ℂ := fun W => if h : ∀ v ∈ W, g v ∈ W then Ψ W h else 0
  have hsub : ∀ (p : Submodule F (Fin d → F) → Prop) [DecidablePred p], (∀ W, p W → ∀ v ∈ W, g v ∈ W) →
      ∀ (hp : ∀ W : { W // p W }, ∀ v ∈ W.1, g v ∈ W.1),
      (∑ᶠ (W : { W // p W }), Ψ W.1 (hp W)) = ∑ W, if p W then Fn W else 0 := by
    intro p _ hpi hp
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter,
      Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun W => by simp) Fn]
    exact Finset.sum_congr rfl fun W _ => (dif_pos (hp W)).symm
  rw [hsub (fun W => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) (fun W h => h.2) (fun W => W.2.2)]
  rw [Finset.sum_congr rfl fun a _ => hsub (fun W => Module.finrank F W = a ∧ ∀ v ∈ W, g v ∈ W)
    (fun W h => h.2) (fun W => W.2.2)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hinv : ∀ v ∈ W, g v ∈ W
  · simp only [and_iff_left hinv]
    rw [Finset.sum_ite_eq]
    have hd : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
    have hiff : W ≠ ⊤ ↔ Module.finrank F W < d := by
      constructor
      · intro h
        have h' := Submodule.finrank_lt h
        rwa [hd] at h'
      · rintro h rfl
        rw [finrank_top, hd] at h
        exact lt_irrefl _ h
    simp only [Finset.mem_range, hiff]
  · simp [hinv]
open Polynomial in
private lemma psi_rootSum_charpoly_mem_virt (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (k : ℕ) (d : ℕ) :
    (fun x : GL (Fin d) F => _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k)
      (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) ∈
      _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin d) F) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  have hconj : ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
      _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) V' (e.conj g) =
        _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) V g :=
    fun V V' _ _ _ _ _ _ e g =>
      _root_.GlobalTheory.CuspGL.psi_conj F _ V V' e g
  have heq : (fun x : GL (Fin d) F => _root_.GlobalTheory.CuspGL.psi
      (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) =
      (fun x : GL (Fin d) F => _root_.GlobalTheory.CuspGL.rootSum θ k (x : Matrix (Fin d) (Fin d) F).charpoly) -
      ∑ a ∈ Finset.range d, (fun x : GL (Fin d) F =>
        ∑ᶠ (W : { W : Submodule F (Fin d → F) // Module.finrank F W = a ∧
          ∀ v ∈ W, (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) v ∈ W }),
          _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (↥(W : Submodule F (Fin d → F)))
            ((Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)).restrict W.2.2)) := by
    funext x
    rw [_root_.GlobalTheory.CuspGL.psi_eq, Matrix.charpoly_toLin',
      finsum_proper_invariant_eq_sum_range_finrank d (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))
        (fun W h => _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (↥W)
          ((Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)).restrict h))]
    simp [Finset.sum_apply]
  rw [heq]
  refine sub_mem (_root_.GlobalTheory.CuspGL.rootSum_charpoly_mem_virt F θ hθ d k)
    (sum_mem fun a ha => ?_)
  exact _root_.GlobalTheory.ParabVirt.parab_virt F
    (fun V _ _ _ g => _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) V g)
    hconj a d (ih a (Finset.mem_range.1 ha))
end GlobalTheory.CuspGL
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
open Polynomial
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d k : ℕ) (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun x : GL (Fin d) F => (-1) ^ (d - 1) *
      _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) ∧
    _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F)) (_root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F)) = _root_.GlobalTheory.CuspGL.glCard F d := by
  obtain ⟨hadd, hX⟩ := _root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k
  have hfr : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  have hfr0 : 0 < Module.finrank F (Fin d → F) := by rw [hfr]; exact hd
  have hip : _root_.GlobalTheory.CuspGL.ipGL
      (_root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F))
      (_root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F)) =
      _root_.GlobalTheory.CuspGL.glCard F d := by
    rw [_root_.GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq F _ _ hadd _
      (_root_.GlobalTheory.CuspGL.isPrimitive_psi F _ _ hadd),
      _root_.GlobalTheory.CuspGL.ipGL_psi_rootSum F _ θ hθ hfr0 k k, hfr]
    have hset : (Finset.range d).filter (fun i => k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) =
        {0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hcong⟩
        by_contra h0
        exact hk i (Nat.pos_of_ne_zero h0) hi hcong
      · rintro rfl
        exact ⟨hd, by simp [Nat.ModEq.refl]⟩
    rw [hset, Finset.card_singleton, Nat.cast_one, mul_one]
  refine ⟨?_, hip⟩
  set ψ : GL (Fin d) F → ℂ := fun x => _root_.GlobalTheory.CuspGL.psi
    (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))
    with hψ
  set χ : GL (Fin d) F → ℂ := fun x => (-1) ^ (d - 1) * ψ x with hχ
  have hψv : ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin d) F) :=
    psi_rootSum_charpoly_mem_virt F θ hθ k d
  have hχv : χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin d) F) := by
    have he : χ = ((-1 : ℤ) ^ (d - 1)) • ψ := by
      funext x
      simp [hχ, zsmul_eq_mul]
    rw [he]
    exact zsmul_mem hψv _
  have hsign : ((-1 : ℂ) ^ (d - 1)) * star ((-1 : ℂ) ^ (d - 1)) = 1 := by
    rw [star_pow, star_neg, star_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hnorm : ∑ᶠ x : GL (Fin d) F, χ x * star (χ x) = (Nat.card (GL (Fin d) F) : ℂ) := by
    have h1 : ∀ x, χ x * star (χ x) = ψ x * star (ψ x) := by
      intro x
      simp only [hχ, star_mul']
      linear_combination (ψ x * star (ψ x)) * hsign
    simp_rw [h1]
    rw [hψ, ← ((_root_.GlobalTheory.CuspGL.extZero_spec F d ψ).2.2.1 _ _), hip]
    rfl
  have hnorm' : ∑ᶠ x : GL (Fin d) F, (-χ) x * star ((-χ) x) = (Nat.card (GL (Fin d) F) : ℂ) := by
    simpa [Pi.neg_apply, star_neg, neg_mul_neg] using hnorm
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hval : χ 1 = ((∏ i ∈ Finset.Ico 1 d, (Nat.card F ^ i - 1) : ℕ) : ℂ) := by
    have h1 : ψ 1 = ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by
      simp only [hψ, Units.val_one, Matrix.toLin'_one]
      rw [← Module.End.one_eq_id, _root_.GlobalTheory.CuspGL.psi_one F _ _ hX hfr0, hfr]
    have h2 : ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) =
        (-1) ^ (d - 1) * ∏ i ∈ Finset.Ico 1 d, ((Nat.card F : ℂ) ^ i - 1) := by
      rw [show ((-1 : ℂ) ^ (d - 1)) = ∏ _i ∈ Finset.Ico 1 d, (-1 : ℂ) by
        rw [Finset.prod_const, Nat.card_Ico], ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    show (-1 : ℂ) ^ (d - 1) * ψ 1 = _
    rw [h1, h2, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul,
      Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hpos : 0 < ∏ i ∈ Finset.Ico 1 d, (Nat.card F ^ i - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have hi1 : i ≠ 0 := by
      have := (Finset.mem_Ico.1 hi).1
      omega
    have := Nat.one_lt_pow hi1 hq
    omega
  have hIrrChar : ∀ φ : GL (Fin d) F → ℂ, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ φ →
      _root_.GlobalTheory.BI.IsChar ℂ ℂ φ := by
    intro φ hφ
    unfold _root_.GlobalTheory.BI.IsIrrChar at hφ
    unfold _root_.GlobalTheory.BI.IsChar
    obtain ⟨n, ρ, -, h⟩ := hφ
    exact ⟨n, ρ, h⟩
  rcases (_root_.GlobalTheory.BI.irr_of_norm_one _ χ hχv hnorm).1 with hirr | hirr
  · exact hIrrChar χ hirr
  · exfalso
    obtain ⟨n, hn, hn1⟩ :=
      ((_root_.GlobalTheory.BI.irr_of_norm_one _ (-χ) (neg_mem hχv) hnorm').2
        (hIrrChar _ hirr)).2
    rw [Pi.neg_apply, hval] at hn1
    have h3 : ((n + ∏ i ∈ Finset.Ico 1 d, (Nat.card F ^ i - 1) : ℕ) : ℂ) = 0 := by
      rw [Nat.cast_add]
      linear_combination -hn1
    rw [Nat.cast_eq_zero] at h3
    omega
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
